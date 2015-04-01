(* Copyright (C) 2013-2014 Matthew Fluet, Brian Leibig.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor LLVMCodegen(S: LLVM_CODEGEN_STRUCTS): LLVM_CODEGEN =
struct

open S

open Machine

datatype z = datatype RealSize.t
datatype z = datatype WordSize.prim

local
   open Runtime
in
   structure GCField = GCField
end

structure Kind =
   struct
      open Kind

      fun isEntry (k: t): bool =
         case k of
            Cont _ => true
          | CReturn {func, ...} => CFunction.mayGC func
          | Func => true
          | Handler _ => true
          | _ => false
   end

structure C =
   struct
      fun args (ss: string list): string
         = concat ("(" :: List.separate (ss, ", ") @ [")"])

      fun callNoSemi (f: string, xs: string list, print: string -> unit): unit
         = (print f
            ; print " ("
            ; (case xs
                  of [] => ()
                | x :: xs => (print x
                              ; List.foreach (xs,
                                             fn x => (print ", "; print x))))
            ; print ")")

      fun call (f, xs, print) =
         (callNoSemi (f, xs, print)
          ; print ";\n")
   end

fun implementsPrim (p: 'a Prim.t): bool =
   let
      datatype z = datatype Prim.Name.t
   in
      case Prim.name p of
         CPointer_add => true
       | CPointer_diff => true
       | CPointer_equal => true
       | CPointer_fromWord => true
       | CPointer_lt => true
       | CPointer_sub => true
       | CPointer_toWord => true
       | FFI_Symbol _ => true
       | Real_Math_acos _ => false
       | Real_Math_asin _ => false
       | Real_Math_atan _ => false
       | Real_Math_atan2 _ => false
       | Real_Math_cos _ => true
       | Real_Math_exp _ => true
       | Real_Math_ln _ => true
       | Real_Math_log10 _ => true
       | Real_Math_sin _ => true
       | Real_Math_sqrt _ => true
       | Real_Math_tan _ => false
       | Real_abs _ => true (* Requires LLVM 3.2 to use "llvm.fabs" intrinsic *)
       | Real_add _ => true
       | Real_castToWord _ => true
       | Real_div _ => true
       | Real_equal _ => true
       | Real_ldexp _ => false
       | Real_le _ => true
       | Real_lt _ => true
       | Real_mul _ => true
       | Real_muladd _ => true
       | Real_mulsub _ => true
       | Real_neg _ => true
       | Real_qequal _ => true
       | Real_rndToReal _ => true
       | Real_rndToWord _ => true
       | Real_round _ => true (* Requires LLVM 3.3 to use "llvm.rint" intrinsic *)
       | Real_sub _ => true
       | Thread_returnToC => false
       | Word_add _ => true
       | Word_addCheck _ => true
       | Word_andb _ => true
       | Word_castToReal _ => true
       | Word_equal _ => true
       | Word_extdToWord _ => true
       | Word_lshift _ => true
       | Word_lt _ => true
       | Word_mul _ => true
       | Word_mulCheck (ws, _) =>
            (case (!Control.Target.arch, ws) of
                (Control.Target.X86, ws) =>
                   (* @llvm.smul.with.overflow.i64 becomes a call to __mulodi4.
                    * @llvm.umul.with.overflow.i64 becomes a call to __udivdi3.
                    * These are provided by compiler-rt and not always by libgcc.
                    * In any case, do not depend on non-standard libraries.
                    *)
                   not (WordSize.equals (ws, WordSize.word64))
              | _ => true)
       | Word_neg _ => true
       | Word_negCheck _ => true
       | Word_notb _ => true
       | Word_orb _ => true
       | Word_quot _ => true
       | Word_rem _ => true
       | Word_rndToReal _ => true
       | Word_rol _ => true
       | Word_ror _ => true
       | Word_rshift _ => true
       | Word_sub _ => true
       | Word_subCheck _ => true
       | Word_xorb _ => true
       | _ => false
   end

structure LLVM =
   struct
      structure Reg =
         struct
            local
               val c = Counter.new 0
            in
               fun tmp () = "%tmp" ^ (Int.toString (Counter.next c))
            end
         end
   end

(* LLVM codegen context. Contains various values/functions that should
   be shared amongst all codegen functions. *)
datatype Context = Context of {
    program: Program.t,
    labelToStringIndex: Label.t -> string,
    chunkLabelToString: ChunkLabel.t -> string,
    chunkLabelIndex: ChunkLabel.t -> int,
    labelChunk: Label.t -> ChunkLabel.t,
    entryLabels: Label.t vector
}

(* WordX.toString converts to hexadecimal, this converts to base 10 *)
fun llwordx (w: WordX.t) =
    IntInf.format (WordX.toIntInf w, StringCvt.DEC)

fun llint (i: int) =
    if i >= 0
    then Int.toString i
    else "-" ^ Int.toString (~ i)

fun llbytes b = llint (Bytes.toInt b)

fun llws (ws: WordSize.t): string =
    case WordSize.prim ws of
        WordSize.W8 => "%Word8"
      | WordSize.W16 => "%Word16"
      | WordSize.W32 => "%Word32"
      | WordSize.W64 => "%Word64"

fun llwsInt (ws: WordSize.t): string =
    case WordSize.prim ws of
        WordSize.W8 => "i8"
      | WordSize.W16 => "i16"
      | WordSize.W32 => "i32"
      | WordSize.W64 => "i64"

fun llrs (rs: RealSize.t): string =
    case rs of
        RealSize.R32 => "%Real32"
      | RealSize.R64 => "%Real64"

(* Reuse CType for LLVM type *)
fun llty (ty: Type.t): string = "%" ^ CType.toString (Type.toCType ty)

fun typeOfGlobal global =
    let
        val t = Type.toCType (Global.ty global)
        val s = CType.toString t
        val number = llint (if Global.isRoot global
                            then Global.numberOfType t
                            else Global.numberOfNonRoot ())
        val array = concat ["[", number, " x %", s, "]"]
    in
        array
    end

(* Makes a two-operand instruction:
 * <lhs> = <opr> <ty> <a0>, <a1>
*)
fun mkinst (lhs, opr, ty, a0, a1) =
    concat ["\t", lhs, " = ", opr, " ", ty, " ", a0, ", ", a1, "\n"]

(* Makes a call to an LLVM math intrinsic function, given a RealSize as rs:
 * <lhs> = call type @llvm.<f>.fX(type <a0>)
*)
fun mkmath (lhs, f, rs, a0) =
    let
        val ty = llrs rs
        val fx = case rs of RealSize.R32 => "f32" | RealSize.R64 => "f64"
    in
        concat ["\t", lhs, " = call ", ty, " @llvm.", f, ".", fx, "(", ty, " ", a0, ")\n"]
    end

(* Makes a conversion instruction:
 * <lhs> = <opr> <fromty> <arg> to <toty>
*)
fun mkconv (lhs, opr, fromty, arg, toty) =
    concat ["\t", lhs, " = ", opr, " ", fromty, " ", arg, " to ", toty, "\n"]

(* Makes a getelementptr instruction:
 * <lhs> = getelementptr inbounds <ty> <arg>, [i32 <idx>]+
 * where <idcs> is a list of integer offsets
 * and <ty> must be a pointer type
 *)
fun mkgep (lhs, ty, arg, idcs) =
    let
        val indices = String.concatWith (List.map (idcs, fn (ity, i) => ity ^ " " ^ i), ", ")
    in
        concat ["\t", lhs, " = getelementptr inbounds ", ty, " ", arg, ", ", indices, "\n"]
    end

(* Makes a load instruction:
 * <lhs> = load <ty> <arg>
 * where <ty> must be a pointer type
 *)
fun mkload (lhs, ty, arg) = concat ["\t", lhs, " = load ", ty, " ", arg, "\n"]

(* Makes a store instruction:
 * store <ty> <arg>, <ty>* <loc>
 * where <ty> is the type of <arg>
 *)
fun mkstore (ty, arg, loc) = concat ["\tstore ", ty, " ", arg, ", ", ty, "* ", loc, "\n"]

fun regName (ty: CType.t, index: int): string =
    concat ["%reg", CType.name ty, "_", Int.toString index]

val cFunctions : string list ref = ref []

fun addCFunction f = if not (List.contains (!cFunctions, f, String.equals))
                     then cFunctions := List.cons (f, !cFunctions)
                     else ()

val ffiSymbols : {name: string, cty: CType.t option, symbolScope: CFunction.SymbolScope.t} list ref = ref []

fun addFfiSymbol s = if not (List.contains (!ffiSymbols, s, fn ({name=n1, ...}, {name=n2, ...}) =>
                             String.equals (n1, n2)))
                     then ffiSymbols := List.cons (s, !ffiSymbols)
                     else ()

fun offsetGCState (gcfield, ty) =
    let
        val castreg = LLVM.Reg.tmp ()
        val cast = mkconv (castreg, "bitcast", "%struct.GC_state*", "@gcState", "%Pointer")
        val ptr = LLVM.Reg.tmp ()
        val gep = mkgep (ptr, "%Pointer", castreg, [("i32", llbytes (GCField.offset gcfield))])
        val ptr2 = LLVM.Reg.tmp ()
        val cast2 = mkconv (ptr2, "bitcast", "%Pointer", ptr, ty)
    in
        (concat [cast, gep, cast2], ptr2)
    end

(* FrontierMem = Frontier *)
fun flushFrontier () =
    let
        val comment = "\t; FlushFrontier\n"
        val (pre, reg) = offsetGCState (GCField.Frontier, "%Pointer*")
        val frontier = LLVM.Reg.tmp ()
        val load = mkload (frontier, "%Pointer*", "%frontier")
        val store = mkstore ("%Pointer", frontier, reg)
    in
        concat [comment, pre, load, store]
    end

(* StackTopMem = StackTop *)
fun flushStackTop () =
    let
        val comment = "\t; FlushStackTop\n"
        val (pre, reg) = offsetGCState (GCField.StackTop, "%Pointer*")
        val stacktop = LLVM.Reg.tmp ()
        val load = mkload (stacktop, "%Pointer*", "%stackTop")
        val store = mkstore ("%Pointer", stacktop, reg)
    in
        concat [comment, pre, load, store]
    end

(* Frontier = FrontierMem *)
fun cacheFrontier () =
    let
        val comment = "\t; CacheFrontier\n"
        val (pre, reg) = offsetGCState (GCField.Frontier, "%Pointer*")
        val frontier = LLVM.Reg.tmp ()
        val load = mkload (frontier, "%Pointer*", reg)
        val store = mkstore ("%Pointer", frontier, "%frontier")
    in
        concat [comment, pre, load, store]
    end

(* StackTop = StackTopMem *)
fun cacheStackTop () =
    let
        val comment = "\t; CacheStackTop\n"
        val (pre, reg) = offsetGCState (GCField.StackTop, "%Pointer*")
        val stacktop = LLVM.Reg.tmp ()
        val load = mkload (stacktop, "%Pointer*", reg)
        val store = mkstore ("%Pointer", stacktop, "%stackTop")
    in
        concat [comment, pre, load, store]
    end

(* l_nextFun = *(uintptr_t* )(StackTop - sizeof(void* ));
   goto top;
 *)
fun callReturn () =
    let
        val comment = "\t; Return\n"
        val stacktop = LLVM.Reg.tmp ()
        val loadst = mkload (stacktop, "%Pointer*", "%stackTop")
        val ptrsize = (llbytes o Bits.toBytes o Control.Target.Size.cpointer) ()
        val ptr = LLVM.Reg.tmp ()
        val gep = mkgep (ptr, "%Pointer", stacktop, [("i32", "-" ^ ptrsize)])
        val castreg = LLVM.Reg.tmp ()
        val cast = mkconv (castreg, "bitcast", "%Pointer", ptr, "%uintptr_t*")
        val loadreg = LLVM.Reg.tmp ()
        val loadofs = mkload (loadreg, "%uintptr_t*", castreg)
        val store = mkstore ("%uintptr_t", loadreg, "%l_nextFun")
        val br = "\tbr label %top\n"
    in
        concat [comment, loadst, gep, cast, loadofs, store, br]
    end

fun stackPush amt =
    let
        val stacktop = LLVM.Reg.tmp ()
        val load = mkload (stacktop, "%Pointer*", "%stackTop")
        val ptr = LLVM.Reg.tmp ()
        val gep = mkgep (ptr, "%Pointer", stacktop, [("i32", amt)])
        val store = mkstore ("%Pointer", ptr, "%stackTop")
        val comment = concat ["\t; Push(", amt, ")\n"]
    in
        concat [comment, load, gep, store]
    end

(* argv - vector of (pre, ty, addr) triples
   i - index of argv
   returns: (pre, type, reg)
 *)
fun getArg (argv, i) =
    if Vector.length argv > i
    then Vector.sub (argv, i)
    else ("", "", "")

(* Converts an operand into its LLVM representation. Returns a triple
 (pre, ty, reg) where

 pre - A string containing preliminary statements that must be
 executed before the register can be referenced

 ty - A string containing the LLVM representation of the register's
 type when dereferenced (meaning reg is really a pointer)

 reg - The register containing a pointer to the value of the operand
 *)
fun getOperandAddr (cxt, operand) =
    case operand of
        Operand.ArrayOffset {base, index, offset, scale, ty} =>
        let
            (* arrayoffset = base + (index * scale) + offset *)
            val (basePre, baseTy, baseReg) = getOperandValue (cxt, base)
            val (indexPre, indexTy, indexReg) = getOperandValue (cxt, index)
            val scl = Scale.toString scale (* "1", "2", "4", or "8" *)
            val scaledIndex = LLVM.Reg.tmp ()
            val scaleIndex = mkinst (scaledIndex, "mul nsw", indexTy, indexReg, scl)
            val ofs = llbytes offset
            val offsettedIndex = LLVM.Reg.tmp ()
            val offsetIndex = mkinst (offsettedIndex, "add nsw", indexTy, scaledIndex, ofs)
            val llvmTy = llty ty
            val ptr = LLVM.Reg.tmp ()
            val gep = mkgep (ptr, baseTy, baseReg, [(indexTy, offsettedIndex)])
            val castedPtr = LLVM.Reg.tmp ()
            val cast = mkconv (castedPtr, "bitcast", baseTy, ptr, llvmTy ^ "*")
        in
            (concat [basePre, indexPre, scaleIndex, offsetIndex, gep, cast], llvmTy, castedPtr)
        end
      | Operand.Contents {oper, ty} =>
        let
            val (operPre, operTy, operReg) = getOperandAddr (cxt, oper)
            val llvmTy = llty ty
            val loaded = LLVM.Reg.tmp ()
            val load = mkload (loaded, operTy ^ "*", operReg)
            val reg = LLVM.Reg.tmp ()
            val cast = mkconv (reg, "bitcast", operTy, loaded, llvmTy ^ "*")
        in
            (concat [operPre, load, cast], llvmTy, reg)
        end
      | Operand.Frontier => ("", "%Pointer", "%frontier")
      | Operand.Global global =>
        let
            val globalType = Global.ty global
            val globalIsRoot = Global.isRoot global
            val globalIndex = Global.index global
            val llvmTy = llty globalType
            val ty = typeOfGlobal global
            val globalID = if globalIsRoot
                           then "@global" ^ CType.toString (Type.toCType globalType)
                           else "@globalObjptrNonRoot"
            val ptr = LLVM.Reg.tmp ()
            val gep = mkgep (ptr, ty ^ "*", globalID, [("i32", "0"), ("i32", llint globalIndex)])
        in
            (gep, llvmTy, ptr)
        end
      | Operand.Offset {base, offset, ty} =>
        let
            val (basePre, baseTy, baseReg) = getOperandValue (cxt, base)
            val idx = llbytes offset
            val llvmTy = llty ty
            val ptr = LLVM.Reg.tmp ()
            val gep = mkgep (ptr, baseTy, baseReg, [("i32", idx)])
            val reg = LLVM.Reg.tmp ()
            val cast = mkconv (reg, "bitcast", baseTy, ptr, llvmTy ^ "*")
        in
            (concat [basePre, gep, cast], llvmTy, reg)
        end
      | Operand.Register register =>
        let
            val regty = Register.ty register
            val reg = regName (Type.toCType regty, Register.index register)
            val ty = llty regty
        in
            ("", ty, reg)
        end
      | Operand.StackOffset stackOffset =>
        let
            val StackOffset.T {offset, ty} = stackOffset
            val idx = llbytes offset
            val stackTop = LLVM.Reg.tmp ()
            val load = mkload (stackTop, "%Pointer*", "%stackTop")
            val gepReg = LLVM.Reg.tmp ()
            val gep = mkgep (gepReg, "%Pointer", stackTop, [("i32", idx)])
            val llvmTy = llty ty
            val reg = LLVM.Reg.tmp ()
            val cast = mkconv (reg, "bitcast", "%Pointer", gepReg, llvmTy ^ "*")
        in
            (concat [load, gep, cast], llvmTy, reg)
        end
      | Operand.StackTop => ("", "%Pointer", "%stackTop")
      | _ => Error.bug ("Cannot get address of " ^ Operand.toString operand)

(* ty is the type of the value *)
and getOperandValue (cxt, operand) =
    let
        fun loadOperand () =
            let
                val (pre, ty, addr) = getOperandAddr (cxt, operand)
                val reg = LLVM.Reg.tmp ()
                val load = mkload (reg, ty ^ "*", addr)
            in
                (pre ^ load, ty, reg)
            end
        val Context { labelToStringIndex, ... } = cxt
    in
        case operand of
            Operand.ArrayOffset _ => loadOperand ()
          | Operand.Cast (oper, ty) =>
            let
                val (operPre, operTy, operReg) =
                   getOperandValue (cxt, oper)
                val llvmTy = llty ty
                val reg = LLVM.Reg.tmp ()
                fun isIntType cty = case cty of
                                            CType.Int8 => true
                                          | CType.Int16 => true
                                          | CType.Int32 => true
                                          | CType.Int64 => true
                                          | CType.Word8 => true
                                          | CType.Word16 => true
                                          | CType.Word32 => true
                                          | CType.Word64 => true
                                          | _ => false
                fun isPtrType cty = case cty of
                                            CType.CPointer => true
                                          | CType.Objptr => true
                                          | _ => false
                val operIsInt = (isIntType o Type.toCType o Operand.ty) oper
                val operIsPtr = (isPtrType o Type.toCType o Operand.ty) oper
                val tyIsInt = (isIntType o Type.toCType) ty
                val tyIsPtr = (isPtrType o Type.toCType) ty
                val operation = if operIsInt andalso tyIsPtr
                                then "inttoptr"
                                else if operIsPtr andalso tyIsInt
                                        then "ptrtoint"
                                        else "bitcast"
                val inst = mkconv (reg, operation, operTy, operReg, llvmTy)
            in
                (concat [operPre, inst], llvmTy, reg)
            end
          | Operand.Contents _ => loadOperand ()
          | Operand.Frontier => loadOperand ()
          | Operand.GCState =>
            let
                val reg = LLVM.Reg.tmp ()
                val cast = mkconv (reg, "bitcast", "%struct.GC_state*", "@gcState", "%Pointer")
            in
                (cast, "%Pointer", reg)
            end
          | Operand.Global _ => loadOperand ()
          | Operand.Label label =>
            let
                val reg = LLVM.Reg.tmp ()
                val cast = mkconv (reg, "inttoptr", "%Word32", labelToStringIndex label,
                                   "%CPointer")
            in
                (cast, "%CPointer", reg)
            end
          | Operand.Null => ("", "i8*", "null")
          | Operand.Offset _ => loadOperand ()
          | Operand.Real real => ("", (llrs o RealX.size) real, RealX.toString real)
          | Operand.Register  _ => loadOperand ()
          | Operand.StackOffset _ => loadOperand ()
          | Operand.StackTop => loadOperand()
          | Operand.Word word => ("", (llws o WordX.size) word, llwordx word)
    end

(* Returns (instruction, ty) pair for the given prim operation *)
fun outputPrim (prim, res, argty, arg0, arg1, arg2) =
    let
        datatype z = datatype Prim.Name.t
    in
        case Prim.name prim of
            CPointer_add =>
            let
                val tmp1 = LLVM.Reg.tmp ()
                val inst1 = mkconv (tmp1, "ptrtoint", "%Pointer", arg0, "%uintptr_t")
                val tmp2 = LLVM.Reg.tmp ()
                val inst2 = mkinst (tmp2, "add", "%uintptr_t", tmp1, arg1)
                val inst3 = mkconv (res, "inttoptr", "%uintptr_t", tmp2, "%Pointer")
            in
                (concat [inst1, inst2, inst3], "%Pointer")
            end
          | CPointer_diff =>
            let
                val tmp1 = LLVM.Reg.tmp ()
                val inst1 = mkconv (tmp1, "ptrtoint", "%Pointer", arg0, "%uintptr_t")
                val tmp2 = LLVM.Reg.tmp ()
                val inst2 = mkconv (tmp2, "ptrtoint", "%Pointer", arg1, "%uintptr_t")
                val inst3 = mkinst (res, "sub", "%uintptr_t", tmp1, tmp2)
            in
                (concat [inst1, inst2, inst3], "%uintptr_t")
            end
          | CPointer_equal =>
            let
                val reg = LLVM.Reg.tmp ()
                val cmp = mkinst (reg, "icmp eq", "%Pointer", arg0, arg1)
                val ext = mkconv (res, "zext", "i1", reg, "%Word32")
            in
                (concat [cmp, ext], "%Word32")
            end
          | CPointer_fromWord =>
            (mkconv (res, "inttoptr", "%uintptr_t", arg0, "%Pointer"), "%Pointer")
          | CPointer_lt =>
            let
                val reg = LLVM.Reg.tmp ()
                val cmp = mkinst (reg, "icmp ult", "%Pointer", arg0, arg1)
                val ext = mkconv (res, "zext", "i1", reg, "%Word32")
            in
                (concat [cmp, ext], "%Word32")
            end
          | CPointer_sub =>
            let
                val tmp1 = LLVM.Reg.tmp ()
                val inst1 = mkconv (tmp1, "ptrtoint", "%Pointer", arg0, "%uintptr_t")
                val tmp2 = LLVM.Reg.tmp ()
                val inst2 = mkinst (tmp2, "sub", "%uintptr_t", tmp1, arg1)
                val inst3 = mkconv (res, "inttoptr", "%uintptr_t", tmp2, "%Pointer")
            in
                (concat [inst1, inst2, inst3], "%Pointer")
            end
          | CPointer_toWord =>
            (mkconv (res, "ptrtoint", "%Pointer", arg0, "%uintptr_t"), "%Pointer")
          | FFI_Symbol (s as {name, cty, ...}) =>
            let
                val () = addFfiSymbol s
                val ty = case cty of
                             SOME t => "%" ^ CType.toString t
                           | NONE => Error.bug ("ffi symbol is void function?") (* TODO *)
                val inst = mkconv (res, "bitcast", ty ^ "*", "@" ^ name, "%Pointer")
            in
                (inst, "%Pointer")
            end
          | Real_Math_cos rs => (mkmath (res, "cos", rs, arg0), llrs rs)
          | Real_Math_exp rs => (mkmath (res, "exp", rs, arg0), llrs rs)
          | Real_Math_ln rs => (mkmath (res, "log", rs, arg0), llrs rs)
          | Real_Math_log10 rs => (mkmath (res, "log10", rs, arg0), llrs rs)
          | Real_Math_sin rs => (mkmath (res, "sin", rs, arg0), llrs rs)
          | Real_Math_sqrt rs => (mkmath (res, "sqrt", rs, arg0), llrs rs)
          | Real_abs rs => (mkmath (res, "fabs", rs, arg0), llrs rs)
          | Real_add rs => (mkinst (res, "fadd", llrs rs, arg0, arg1), llrs rs)
          | Real_castToWord (rs, ws) =>
            (case rs of
                 R32 => if WordSize.equals (ws, WordSize.word32)
                        then (mkconv (res, "bitcast", "float", arg0, "i32"), "i32")
                        else Error.bug "LLVM codegen: Real_castToWord"
               | R64 => if WordSize.equals (ws, WordSize.word64)
                        then (mkconv (res, "bitcast", "double", arg0, "i64"), "i64")
                        else Error.bug "LLVM codegen: Real_castToWord")
          | Real_div rs => (mkinst (res, "fdiv", llrs rs, arg0, arg1), llrs rs)
          | Real_equal rs =>
            let
                val reg = LLVM.Reg.tmp ()
                val cmp = mkinst (reg, "fcmp oeq", llrs rs, arg0, arg1)
                val ext = mkconv (res, "zext", "i1", reg, "%Word32")
            in
                (concat [cmp, ext], "%Word32")
            end
          | Real_le rs =>
            let
                val reg = LLVM.Reg.tmp ()
                val cmp = mkinst (reg, "fcmp ole", llrs rs, arg0, arg1)
                val ext = mkconv (res, "zext", "i1", reg, "%Word32")
            in
                (concat [cmp, ext], "%Word32")
            end
          | Real_lt rs =>
            let
                val reg = LLVM.Reg.tmp ()
                val cmp = mkinst (reg, "fcmp olt", llrs rs, arg0, arg1)
                val ext = mkconv (res, "zext", "i1", reg, "%Word32")
            in
                (concat [cmp, ext], "%Word32")
            end
          | Real_mul rs => (mkinst (res, "fmul", llrs rs, arg0, arg1), llrs rs)
          | Real_muladd rs =>
            let
                val size = case rs of
                               RealSize.R32 => "f32"
                             | RealSize.R64 => "f64"
                val llsize = llrs rs
                val inst = concat ["\t", res, " = call ", llsize, " @llvm.fma.", size, "(",
                                   llsize, " ", arg0, ", ", llsize, " ",
                                   arg1, ", ", llsize, " ", arg2, ")\n"]
            in
                (inst, llsize)
            end
          | Real_mulsub rs =>
            let
                val size = case rs of
                               RealSize.R32 => "f32"
                             | RealSize.R64 => "f64"
                val llsize = llrs rs
                val tmp1 = LLVM.Reg.tmp ()
                val inst1 = mkinst (tmp1, "fsub", llsize, "-0.0", arg2)
                val inst2 = concat ["\t", res, " = call ", llsize, " @llvm.fma.", size, "(",
                                    llsize, " ", arg0, ", ", llsize, " ",
                                    arg1, ", ", llsize, " ", tmp1, ")\n"]
            in
                (concat [inst1, inst2], llsize)
            end
          | Real_neg rs => (mkinst (res, "fsub", llrs rs, "-0.0", arg0), llrs rs)
          | Real_qequal rs =>
            let
                val reg = LLVM.Reg.tmp ()
                val cmp = mkinst (reg, "fcmp ueq", llrs rs, arg0, arg1)
                val ext = mkconv (res, "zext", "i1", reg, "%Word32")
            in
                (concat [cmp, ext], "%Word32")
            end
          | Real_rndToReal rs =>
            (case rs of
                 (RealSize.R64, RealSize.R32) =>
                 (mkconv (res, "fptrunc", "double", arg0, "float"), "float")
               | (RealSize.R32, RealSize.R64) =>
                 (mkconv (res, "fpext", "float", arg0, "double"), "double")
               | (RealSize.R32, RealSize.R32) => (* this is a no-op *)
                 (mkconv (res, "bitcast", "float", arg0, "float"), "float")
               | (RealSize.R64, RealSize.R64) => (* this is a no-op *)
                 (mkconv (res, "bitcast", "double", arg0, "double"), "double"))
          | Real_rndToWord (rs, ws, {signed}) =>
            let
                val opr = if signed then "fptosi" else "fptoui"
            in
                (mkconv (res, opr, llrs rs, arg0, llws ws), llws ws)
            end
          | Real_round rs => (mkmath (res, "rint", rs, arg0), llrs rs)
          | Real_sub rs => (mkinst (res, "fsub", llrs rs, arg0, arg1), llrs rs)
          | Thread_returnToC =>
            let
                val store = mkstore ("i32", "1", "@returnToC")
                val ret = "\tret %struct.cont %cont\n"
            in
                (concat [store, ret], "")
            end
          | Word_add ws => (mkinst (res, "add", llws ws, arg0, arg1), llws ws)
          | Word_addCheck (ws, {signed}) =>
            let
                val opr = if signed then "sadd" else "uadd"
                val ty = llws ws
                val inst = concat ["\t", res, " = call {", ty, ", i1} @llvm.", opr,
                                   ".with.overflow.", llwsInt ws, "(", ty, " ", arg0,
                                   ", ", ty, " ", arg1, ")\n"]
            in
                (inst, concat ["{", ty, ", i1}"])
            end
          | Word_andb ws => (mkinst (res, "and", llws ws, arg0, arg1), llws ws)
          | Word_castToReal (ws, rs) =>
            (case rs of
                 R32 => if WordSize.equals (ws, WordSize.word32)
                        then (mkconv (res, "bitcast", "i32", arg0, "float"), "float")
                        else Error.bug "LLVM codegen: Word_castToReal"
               | R64 => if WordSize.equals (ws, WordSize.word64)
                        then (mkconv (res, "bitcast", "i64", arg0, "double"), "double")
                        else Error.bug "LLVM codegen: Word_castToReal")
          | Word_equal _ =>
            let
                val reg = LLVM.Reg.tmp ()
                val cmp = mkinst (reg, "icmp eq", argty, arg0, arg1)
                val ext = mkconv (res, "zext", "i1", reg, "%Word32")
            in
                (concat [cmp, ext], "%Word32")
            end
          | Word_extdToWord (ws1, ws2, {signed}) =>
            let
                val opr = case WordSize.compare (ws1, ws2) of
                              LESS => if signed then "sext" else "zext"
                            | EQUAL => Error.bug "LLVM codegen: Word_extdToWord"
                            | GREATER => "trunc"
            in
                (mkconv (res, opr, llws ws1, arg0, llws ws2), llws ws2)
            end
          | Word_lshift ws => (mkinst (res, "shl", llws ws, arg0, arg1), llws ws)
          | Word_lt (ws, {signed}) =>
            let
                val reg = LLVM.Reg.tmp ()
                val cmp = mkinst (reg, if signed then "icmp slt" else "icmp ult",
                                  llws ws, arg0, arg1)
                val ext = mkconv (res, "zext", "i1", reg, "%Word32")
            in
                (concat [cmp, ext], "%Word32")
            end
          | Word_mul (ws, _) => (mkinst (res, "mul", llws ws, arg0, arg1), llws ws)
          | Word_mulCheck (ws, {signed}) =>
            let
                val opr = if signed then "smul" else "umul"
                val ty = llws ws
                val inst = concat ["\t", res, " = call {", ty, ", i1} @llvm.", opr,
                                   ".with.overflow.", llwsInt ws, "(", ty, " ", arg0,
                                   ", ", ty, " ", arg1, ")\n"]
            in
                (inst, concat ["{", ty, ", i1}"])
            end
          | Word_neg ws => (mkinst (res, "sub", llws ws, "0", arg0), llws ws)
          | Word_negCheck ws =>
            let
                val ty = llws ws
                val inst = concat ["\t", res, " = call {", ty, ", i1} @llvm.ssub.with.overflow.",
                                   llwsInt ws, "(", ty, " 0, ", ty, " ", arg0, ")\n"]
                val resTy = concat ["{", ty, ", i1}"]
            in
                (inst, resTy)
            end
          | Word_notb ws => (mkinst (res, "xor", llws ws, arg0, "-1"), llws ws)
          | Word_orb ws => (mkinst (res, "or", llws ws, arg0, arg1), llws ws)
          | Word_quot (ws, {signed}) =>
            (mkinst (res, if signed then "sdiv" else "udiv", llws ws, arg0, arg1), llws ws)
          | Word_rem (ws, {signed}) =>
            (mkinst (res, if signed then "srem" else "urem", llws ws, arg0, arg1), llws ws)
          | Word_rndToReal (ws, rs, {signed}) =>
            let
                val opr = if signed then "sitofp" else "uitofp"
            in
                (mkconv (res, opr, llws ws, arg0, llrs rs), llrs rs)
            end
          | Word_rol ws =>
            let
                (* (arg0 >> (size - arg1)) | (arg0 << arg1) *)
                val ty = llws ws
                val tmp1 = LLVM.Reg.tmp ()
                val inst1 = mkinst (tmp1, "sub", ty, WordSize.toString ws, arg1)
                val tmp2 = LLVM.Reg.tmp ()
                val inst2 = mkinst (tmp2, "lshr", ty, arg0, tmp1)
                val tmp3 = LLVM.Reg.tmp ()
                val inst3 = mkinst (tmp3, "shl", ty, arg0, arg1)
                val inst4 = mkinst (res, "or", ty, tmp2, tmp3)
            in
                (concat [inst1, inst2, inst3, inst4], llws ws)
            end
          | Word_ror ws =>
            let
                (* (arg0 >> arg1) | (arg0 << (size - arg1)) *)
                val ty = llws ws
                val tmp1 = LLVM.Reg.tmp ()
                val inst1 = mkinst (tmp1, "lshr", ty, arg0, arg1)
                val tmp2 = LLVM.Reg.tmp ()
                val inst2 = mkinst (tmp2, "sub", ty, WordSize.toString ws, arg1)
                val tmp3 = LLVM.Reg.tmp ()
                val inst3 = mkinst (tmp3, "shl", ty, arg0, tmp2)
                val inst4 = mkinst (res, "or", ty, tmp1, tmp3)
            in
                (concat [inst1, inst2, inst3, inst4], llws ws)
            end
          | Word_rshift (ws, {signed}) =>
            let
                val opr = if signed then "ashr" else "lshr"
            in
                (mkinst (res, opr, llws ws, arg0, arg1), llws ws)
            end
          | Word_sub ws => (mkinst (res, "sub", llws ws, arg0, arg1), llws ws)
          | Word_subCheck (ws, {signed}) =>
            let
                val opr = if signed then "ssub" else "usub"
                val ty = llws ws
                val inst = concat ["\t", res, " = call {", ty, ", i1} @llvm.", opr,
                                   ".with.overflow.", llwsInt ws, "(", ty, " ", arg0,
                                   ", ", ty, " ", arg1, ")\n"]
            in
                (inst, concat ["{", ty, ", i1}"])
            end
          | Word_xorb ws => (mkinst (res, "xor", llws ws, arg0, arg1), llws ws)
          | _ => Error.bug "LLVM Codegen: Unsupported operation in outputPrim"
    end

fun outputPrimApp (cxt, p) =
    let
        datatype z = datatype Prim.Name.t
        val {args, dst, prim} = p
        fun typeOfArg0 () = (WordSize.fromBits o Type.width o Operand.ty o Vector.sub) (args, 0)
        val castArg1 = case Prim.name prim of
                           Word_rshift _ => SOME (typeOfArg0 ())
                         | Word_lshift _ => SOME (typeOfArg0 ())
                         | Word_rol _ => SOME (typeOfArg0 ())
                         | Word_ror _ => SOME (typeOfArg0 ())
                         | _ => NONE
        val operands = Vector.map (args, fn opr => getOperandValue (cxt, opr))
        val (arg0pre, arg0ty, arg0reg) = getArg (operands, 0)
        val (arg1pre, _, arg1) = getArg (operands, 1)
        val (cast, arg1reg) = case castArg1 of
                                  SOME ty =>
                                  let
                                      val reg = LLVM.Reg.tmp ()
                                      val opr = case WordSize.prim ty of
                                                    WordSize.W8 => "trunc"
                                                  | WordSize.W16 => "trunc"
                                                  | WordSize.W32 => "bitcast"
                                                  | WordSize.W64 => "zext"
                                      val inst = mkconv (reg, opr, "%Word32", arg1, llws ty)
                                  in
                                      (inst, reg)
                                  end
                                | NONE => ("", arg1)
        val (arg2pre, _, arg2reg) = getArg (operands, 2)
        val reg = LLVM.Reg.tmp ()
        val (inst, _) = outputPrim (prim, reg, arg0ty, arg0reg, arg1reg, arg2reg)
        val storeDest =
            case dst of
                NONE => ""
              | SOME dest =>
                let
                    val (destPre, destTy, destReg) = getOperandAddr (cxt, dest)
                    val store = mkstore (destTy, reg, destReg)
                in
                    concat [destPre, store]
                end
    in
        concat [arg0pre, arg1pre, cast, arg2pre, inst, storeDest]
    end

fun outputTransfer (cxt, transfer, srcChunk) =
    let
        val comment = concat ["\t; ", Layout.toString (Transfer.layout transfer), "\n"]
        val Context { labelToStringIndex = labelToStringIndex,
                      chunkLabelToString = chunkLabelToString,
                      labelChunk = labelChunk, ... } = cxt
        fun transferPush (return, size) =
            let
                val offset = llbytes (Bytes.- (size, Runtime.labelSize ()))
                val frameIndex = labelToStringIndex return
                val stackTop = LLVM.Reg.tmp ()
                val load = mkload (stackTop, "%Pointer*", "%stackTop")
                val gepReg = LLVM.Reg.tmp ()
                val gep = mkgep (gepReg, "%Pointer", stackTop, [("i32", offset)])
                val castreg = LLVM.Reg.tmp ()
                val cast = mkconv (castreg, "bitcast", "%Pointer", gepReg, "%uintptr_t*")
                val storeIndex = mkstore ("%uintptr_t", frameIndex, castreg)
                val pushcode = stackPush (llbytes size)
            in
                concat [load, gep, cast, storeIndex, pushcode]
            end
    in
        case transfer of
            Transfer.Arith {args, dst, overflow, prim, success} =>
            let
                val overflowstr = Label.toString overflow
                val successstr = Label.toString success
                val operands = Vector.map (args, fn opr => getOperandValue (cxt, opr))
                val (arg0pre, arg0ty, arg0reg) = getArg (operands, 0)
                val (arg1pre, _, arg1reg) = getArg (operands, 1)
                val (arg2pre, _, arg2reg) = getArg (operands, 2)
                val reg = LLVM.Reg.tmp ()
                val (inst, ty) = outputPrim (prim, reg, arg0ty, arg0reg, arg1reg, arg2reg)
                val res = LLVM.Reg.tmp ()
                val extractRes = concat ["\t", res, " = extractvalue ", ty, " ", reg, ", 0\n"]
                val obit = LLVM.Reg.tmp ()
                val extractObit = concat ["\t", obit, " = extractvalue ", ty, " ", reg, ", 1\n"]
                val (destPre, destTy, destReg) = getOperandAddr (cxt, dst)
                val store = mkstore (destTy, res, destReg)
                val br = concat ["\tbr i1 ", obit, ", label %",
                                 overflowstr, ", label %", successstr, "\n"]
            in
                concat [comment, arg0pre, arg1pre, arg2pre, inst,
                        extractRes, extractObit, destPre, store, br]
            end
          | Transfer.CCall {args, frameInfo, func, return} =>
            let
                val CFunction.T {maySwitchThreads,
                                 modifiesFrontier,
                                 readsStackTop,
                                 return = returnTy,
                                 target,
                                 writesStackTop, ...} = func
                val (paramPres, paramTypes, paramRegs) =
                    Vector.unzip3 (Vector.map (args, fn opr => getOperandValue (cxt, opr)))
                val push =
                    case frameInfo of
                        NONE => ""
                      | SOME fi =>
                        let
                            val Context { program = program, ... } = cxt
                            val size = Program.frameSize (program, fi)
                        in
                            transferPush (valOf return, size)
                        end
                val flushFrontierCode = if modifiesFrontier then flushFrontier () else ""
                val flushStackTopCode = if readsStackTop then flushStackTop () else ""
                val resultReg = if Type.isUnit returnTy then "" else LLVM.Reg.tmp ()
                val call = case target of
                               CFunction.Target.Direct name =>
                               let
                                   val (lhs, ty) = if Type.isUnit returnTy
                                                   then ("\t", "void")
                                                   else (concat ["\t", resultReg, " = "],
                                                         llty returnTy)
                                   val llparams = String.concatWith
                                                      (Vector.toListMap
                                                           (Vector.zip (paramTypes, paramRegs),
                                                            fn (t, p) => t ^ " " ^ p),
                                                       ", ")
                                   val cfunc = concat [ty, " @", name, "(",
                                                       String.concatWith
                                                           ((Vector.toList paramTypes), ", "),
                                                       ")"]
                                   val () = addCFunction cfunc
                               in
                                   concat [lhs, "call ", ty, " @", name, "(", llparams, ")\n"]
                               end
                             | CFunction.Target.Indirect => (* TODO *) ""
                val epilogue = case return of
                                   NONE => "\tunreachable\n"
                                 | SOME l =>
                                   let
                                       val storeResult = if Type.isUnit returnTy
                                                         then ""
                                                         else mkstore (llty returnTy, resultReg,
                                                                       "@CReturn" ^ CType.name (Type.toCType returnTy))
                                       val cacheFrontierCode = if modifiesFrontier
                                                               then cacheFrontier ()
                                                               else ""
                                       val cacheStackTopCode = if writesStackTop
                                                               then cacheStackTop ()
                                                               else ""
                                       val br = if maySwitchThreads
                                                then callReturn ()
                                                else concat ["\tbr label %", Label.toString l,
                                                             "\n"]
                                   in
                                       concat [storeResult, cacheFrontierCode, cacheStackTopCode,
                                               br]
                                   end
            in
                concat [comment,
                        "\t; GetOperands\n",
                        String.concatV paramPres,
                        push,
                        flushFrontierCode,
                        flushStackTopCode,
                        "\t; Call\n",
                        call,
                        epilogue]
            end
          | Transfer.Call {label, return, ...} =>
            let
                val labelstr = Label.toString label
                val dstChunk = labelChunk label
                val push = case return of
                               NONE => ""
                             | SOME {return, size, ...} => transferPush (return, size)
                val goto = if ChunkLabel.equals (srcChunk, dstChunk)
                           then concat ["\tbr label %", labelstr, "\n"]
                           else let
                               val comment = "\t; FarJump\n"
                               (* nextFun = l *)
                               val storeNF = mkstore ("%uintptr_t", labelToStringIndex label,
                                                      "%l_nextFun")
                               val br = "\tbr label %exit\n"
                           in
                               concat [comment, storeNF, br]
                           end
            in
                concat [push, goto]
            end
          | Transfer.Goto label =>
            let
                val labelString = Label.toString label
                val goto = concat ["\tbr label %", labelString, "\n"]
            in
                concat [comment, goto]
            end
          | Transfer.Raise =>
            let
                (* StackTop = StackBottom + ExnStack *)
                val (sbpre, sbreg) = offsetGCState (GCField.StackBottom, "%Pointer*")
                val stackBottom = LLVM.Reg.tmp ()
                val loadStackBottom = mkload (stackBottom, "%Pointer*", sbreg)
                val (espre, esreg) = offsetGCState (GCField.ExnStack, "i32*")
                val exnStack = LLVM.Reg.tmp ()
                val loadExnStack = mkload (exnStack, "i32*", esreg)
                val sum = LLVM.Reg.tmp ()
                val gep = mkgep (sum, "%Pointer", stackBottom, [("i32", exnStack)])
                val store = mkstore ("%Pointer", sum, "%stackTop")
                (* l_nextFun = *(uintptr_t* )(StackTop - sizeof(void* )); *)
                val stackTop = LLVM.Reg.tmp ()
                val loadStackTop = mkload (stackTop, "%Pointer*", "%stackTop")
                val sizeofptr = (Bytes.toString o Bits.toBytes o Control.Target.Size.cpointer) ()
                val offsetST = LLVM.Reg.tmp ()
                val subPtrSize = mkgep (offsetST, "%Pointer", stackTop, [("i32", "-" ^ sizeofptr)])
                val offsetIntPtr = LLVM.Reg.tmp ()
                val toint = mkconv (offsetIntPtr, "bitcast", "%Pointer", offsetST,
                                    "%uintptr_t*")
                val offsetInt = LLVM.Reg.tmp ()
                val loadOffset = mkload (offsetInt, "%uintptr_t*", offsetIntPtr)
                val storeLNF = mkstore ("%uintptr_t", offsetInt, "%l_nextFun")
                (* goto top *)
                val gotoTop = "\tbr label %top\n"
            in
                concat [comment, sbpre, loadStackBottom, espre, loadExnStack, gep, store,
                        loadStackTop, subPtrSize, toint, loadOffset, storeLNF, gotoTop]
            end
          | Transfer.Return => callReturn ()
          | Transfer.Switch switch =>
            let
                val Switch.T {cases, default, test, ...} = switch
                val (testpre, testty, testreg) = getOperandValue (cxt, test)
                fun branch (ifTrue, ifFalse) =
                    let
                        val testi1 = LLVM.Reg.tmp ()
                        val trunc = mkconv (testi1, "trunc", testty, testreg, "i1")
                        val br = concat ["\tbr i1 ", testi1,
                                         ", label %", Label.toString ifTrue,
                                         ", label %", Label.toString ifFalse, "\n"]
                    in
                        concat [comment, testpre, trunc, br]
                    end
                fun switch () =
                    let
                        val (switchCases, switchDefault) =
                            case default of
                                SOME d => (cases, "%" ^ Label.toString d)
                              | NONE => (Vector.dropPrefix (cases, 1),
                                         "%" ^ Label.toString (#2 (Vector.sub (cases, 0))))
                        val branches = String.concatV (Vector.map (switchCases, fn (w, l) =>
                                           concat ["\t\t", llws (WordX.size w), " ", llwordx w,
                                                   ", label %", Label.toString l, "\n"]))
                        val switch = concat ["\tswitch ", testty, " ", testreg,
                                             ", label ", switchDefault, " [\n", branches, "\t]\n"]
                    in
                        concat [comment, testpre, switch]
                    end
            in
                if Vector.length cases = 2 andalso Option.isNone default
                then
                    let
                        val (c0, l0) = Vector.sub (cases, 0)
                        val (c1, l1) = Vector.sub (cases, 1)
                    in
                        if WordX.isZero c0 andalso WordX.isOne c1
                        then branch (l1, l0)
                        else if WordX.isZero c1 andalso WordX.isZero c0
                             then branch (l0, l1)
                             else switch ()
                    end
                else switch ()
            end
    end

fun emitChunk {context, chunk, outputLL} =
   let
      val () = cFunctions := []
      val () = ffiSymbols := []

      val Context {labelToStringIndex, chunkLabelIndex, labelChunk,
                   chunkLabelToString, entryLabels, program, ... } = context

      val Chunk.T {blocks, chunkLabel, regMax} = chunk

      val {done, print, file = _} = outputLL ()
      val prints = fn ss => List.foreach (ss, print)

      val unreachableLabel = Label.newString "unreachable"

      fun operandToAddr oper =
         case oper of
            Operand.ArrayOffset {base, index, offset, scale, ty} =>
               let
                  val (baseTy, baseReg) = operandToValue base
                  val (indexTy, indexReg) = operandToValue index
                  val indexScale = LLVM.Reg.tmp ()
                  val () = print (mkinst (indexScale,
                                          "mul", indexTy,
                                          indexReg, Scale.toString scale))
                  val indexScalePlusOffset = LLVM.Reg.tmp ()
                  val () = print (mkinst (indexScalePlusOffset,
                                          "add", indexTy,
                                          indexScale, llbytes offset))
                  val ptr = LLVM.Reg.tmp ()
                  val () = print (mkgep (ptr, baseTy, baseReg,
                                         [(indexTy, indexScalePlusOffset)]))
                  val resTy = llty ty
                  val res = LLVM.Reg.tmp ()
                  val () = print (mkconv (res, "bitcast", baseTy, ptr, resTy ^ "*"))
               in
                  (resTy, res)
               end
          | Operand.Contents {oper, ty} =>
               let
                  val (operTy, operReg) = operandToAddr oper
                  val tmp = LLVM.Reg.tmp ()
                  val () = print (mkload (tmp, operTy ^ "*", operReg))
                  val resTy = llty ty
                  val res = LLVM.Reg.tmp ()
                  val () = print (mkconv (res, "bitcast", operTy, tmp, resTy ^ "*"))
               in
                  (resTy, res)
               end
          | Operand.Frontier => ("%Pointer", "%frontier")
          | Operand.Global global =>
               let
                  val globalTy = Global.ty global
                  val globalIdx = Global.index global
                  val globalArrTy = typeOfGlobal global
                  val globalArrPtr =
                     if Global.isRoot global
                        then concat ["@global", CType.toString (Type.toCType globalTy)]
                     else "@globalObjptrNonRoot"
                  val resTy = llty globalTy
                  val res = LLVM.Reg.tmp ()
                  val () = print (mkgep (res, globalArrTy ^ "*", globalArrPtr,
                                         [("i32", "0"), ("i32", Int.toString globalIdx)]))
               in
                  (resTy, res)
               end
          | Operand.Offset {base, offset, ty} =>
               let
                  val (baseTy, baseReg) = operandToValue base
                  val ptr = LLVM.Reg.tmp ()
                  val () = print (mkgep (ptr, baseTy, baseReg, [("i32", llbytes offset)]))
                  val resTy = llty ty
                  val res = LLVM.Reg.tmp ()
                  val () = print (mkconv (res, "bitcast", baseTy, ptr, resTy ^ "*"))
               in
                  (resTy, res)
               end
          | Operand.Register reg =>
               let
                  val regTy = Register.ty reg
                  val regIdx = Register.index reg
                  val resTy = llty regTy
                  val res = concat ["%reg", CType.name (Type.toCType regTy),
                                    "_", Int.toString regIdx]
               in
                  (resTy, res)
               end
          | Operand.StackOffset stackOffset =>
               let
                  val StackOffset.T {offset, ty} = stackOffset
                  val (_, stackTop) = operandToValue (Operand.StackTop)
                  val ptr = LLVM.Reg.tmp ()
                  val () = print (mkgep (ptr, "%Pointer", stackTop, [("i32", llbytes offset)]))
                  val resTy = llty ty
                  val res = LLVM.Reg.tmp ()
                  val () = print (mkconv (res, "bitcast", "%Pointer", ptr, resTy ^ "*"))
               in
                  (resTy, res)
               end
          | Operand.StackTop => ("%Pointer", "%stackTop")
          | _ => Error.bug ("LLVMCodegen.emitChunk.operandToAddr: " ^ Operand.toString oper)

      and operandToValue oper =
         let
            fun loadOper () =
               let
                  val (resTy, addrReg) = operandToAddr oper
                  val res = LLVM.Reg.tmp ()
                  val () = print (mkload (res, resTy ^ "*", addrReg))
               in
                  (resTy, res)
               end
         in
            case oper of
               Operand.ArrayOffset _ => loadOper ()
             | Operand.Cast (oper, ty) =>
                  let
                     val (operTy, operReg) = operandToValue oper
                     val resTy = llty ty
                     val res = LLVM.Reg.tmp ()
                     fun isIntTy ty =
                        case Type.toCType ty of
                           CType.Int8 => true
                         | CType.Int16 => true
                         | CType.Int32 => true
                         | CType.Int64 => true
                         | CType.Word8 => true
                         | CType.Word16 => true
                         | CType.Word32 => true
                         | CType.Word64 => true
                         | _ => false
                     fun isPtrTy ty =
                        case Type.toCType ty of
                           CType.CPointer => true
                         | CType.Objptr => true
                         | _ => false
                     val operIsIntTy = (isIntTy o Operand.ty) oper
                     val operIsPtrTy = (isPtrTy o Operand.ty) oper
                     val resIsIntTy = isIntTy ty
                     val resIsPtrTy = isPtrTy ty
                     val instr =
                        if operIsIntTy andalso resIsPtrTy
                           then "inttoptr"
                        else if operIsPtrTy andalso resIsIntTy
                           then "ptrtoint"
                        else "bitcast"
                     val () = print (mkconv (res, instr, operTy, operReg, resTy))
                  in
                     (resTy, res)
                  end
             | Operand.Contents _ => loadOper ()
             | Operand.Frontier => loadOper ()
             | Operand.GCState =>
                  let
                     val res = LLVM.Reg.tmp ()
                     val () = print (mkconv (res, "bitcast", "%struct.GC_state*", "@gcState", "%Pointer"))
                  in
                     ("%Pointer", res)
                  end
             | Operand.Global _ => loadOper ()
             | Operand.Label label =>
                  let
                     val res = LLVM.Reg.tmp ()
                     val () = print (mkconv (res, "inttoptr", "%Word32", labelToStringIndex label, "%CPointer"))
                  in
                     ("%CPointer", res)
                  end
             | Operand.Null => ("i8*", "null")
             | Operand.Offset _ => loadOper ()
             | Operand.Real real =>
                  let
                     val resTy = llrs (RealX.size real)
                     val res = LLVM.Reg.tmp ()
                     val () = print (mkconv (res, "bitcast", resTy, RealX.toString real, resTy))
                  in
                     (resTy, res)
                  end
             | Operand.Register  _ => loadOper ()
             | Operand.StackOffset _ => loadOper ()
             | Operand.StackTop => loadOper ()
             | Operand.Word word =>
                  let
                     val resTy = llws (WordX.size word)
                     val res = LLVM.Reg.tmp ()
                     val () = print (mkconv (res, "bitcast", resTy, llwordx word, resTy))
                  in
                     (resTy, res)
                  end
         end

      fun emitPrimApp {args, prim} =
         let
            val arg = fn i => Vector.sub (args, i)
            val argTy = #1 o arg
            val argReg = #2 o arg

            fun doBinAL instr =
               let
                  val resTy = argTy 0
                  val res = LLVM.Reg.tmp ()
                  val () = print (mkinst (res, instr, resTy, argReg 0, argReg 1))
               in
                  (resTy, res)
               end
            fun doCmp instr =
               let
                  val (_, tmp) = doBinAL instr
                  val resTy = "%Word32"
                  val res = LLVM.Reg.tmp ()
                  val () = print (mkconv (res, "zext", "i1", tmp, resTy))
               in
                  (resTy, res)
               end
            fun doConv (conv, resTy) =
               let
                  val res = LLVM.Reg.tmp ()
                  val () = print (mkconv (res, conv, argTy 0, argReg 0, resTy))
               in
                  (resTy, res)
               end
            fun doCall (call, resTy, args) =
               let
                  val res = LLVM.Reg.tmp ()
                  val args = Vector.toListMap (args, fn (argTy, argReg) => argTy ^ " " ^ argReg)
                  val args = String.concatWith (args, ",")
                  val () = prints ["\t", res, " = call ", resTy, " ", call,
                                   "(", args, ")\n"]
               in
                  (resTy, res)
               end
            fun doCheckCall (call, ws) =
               let val ws = WordSize.toString ws
               in doCall ("@llvm." ^ call ^ ".with.overflow.i" ^ ws, "{%Word" ^ ws ^ ",i1}", args)
               end
            fun doMathCall (call, rs) =
               let val rs = RealSize.toString rs
               in doCall ("@llvm." ^ call ^ ".f" ^ rs, "%Real" ^ rs, args)
               end
            datatype z = datatype Prim.Name.t
         in
            case Prim.name prim of
               CPointer_add =>
                  let
                     val tmp0 = emitPrimApp {args = Vector.new1 (arg 0), prim = Prim.cpointerToWord}
                     val tmp = emitPrimApp {args = Vector.new2 (tmp0, arg 1), prim = Prim.wordAdd (WordSize.cptrdiff())}
                     val res = emitPrimApp {args = Vector.new1 tmp, prim = Prim.cpointerFromWord}
                  in
                     res
                  end
(*
               CPointer_add =>
                  let
                     val resTy = argTy 0
                     val res = LLVM.Reg.tmp ()
                     val () = print (mkgep (res, argTy 0, argReg 0, [arg 1]))
                  in
                     (resTy, res)
                  end
*)
             | CPointer_diff =>
                  let
                     val tmp0 = emitPrimApp {args = Vector.new1 (arg 0), prim = Prim.cpointerToWord}
                     val tmp1 = emitPrimApp {args = Vector.new1 (arg 1), prim = Prim.cpointerToWord}
                     val res = emitPrimApp {args = Vector.new2 (tmp0, tmp1), prim = Prim.wordSub (WordSize.cptrdiff ())}
                  in
                     res
                  end
             | CPointer_equal => doCmp "icmp eq"
             | CPointer_fromWord => doConv ("inttoptr", "%CPointer")
             | CPointer_lt => doCmp "icmp ult"
             | CPointer_sub =>
                  let
                     val tmp0 = emitPrimApp {args = Vector.new1 (arg 0), prim = Prim.cpointerToWord}
                     val tmp = emitPrimApp {args = Vector.new2 (tmp0, arg 1), prim = Prim.wordSub (WordSize.cptrdiff())}
                     val res = emitPrimApp {args = Vector.new1 tmp, prim = Prim.cpointerFromWord}
                  in
                     res
                  end
(*
             | CPointer_sub =>
                  let
                     val tmp = emitPrimApp {args = Vector.new1 (arg 1), prim = Prim.wordNeg (WordSize.cptrdiff ())}
                     val res = emitPrimApp {args = Vector.new2 (arg 0, tmp), prim = Prim.cpointerAdd}
                  in
                     res
                  end
*)
             | CPointer_toWord => doConv ("ptrtoint", "%Word" ^ (WordSize.toString (WordSize.cpointer ())))
             | FFI_Symbol (s as {name, cty, ...}) =>
                  let
                     val () = addFfiSymbol s
                     val symTy =
                        case cty of
                           SOME cty => "%" ^ CType.toString cty ^ "*"
                         | NONE => "%CPointer"
                     val resTy = "%CPointer"
                     val res = LLVM.Reg.tmp ()
                     val () = print (mkconv (res, "bitcast", symTy, "@" ^ name, resTy))
                  in
                     (resTy, res)
                  end
             (*
             | Real_Math_acos _ => false
             | Real_Math_asin _ => false
             | Real_Math_atan _ => false
             | Real_Math_atan2 _ => false
             *)
             | Real_Math_cos rs => doMathCall ("cos", rs)
             | Real_Math_exp rs => doMathCall ("exp", rs)
             | Real_Math_ln rs => doMathCall ("log", rs)
             | Real_Math_log10 rs => doMathCall ("log10", rs)
             | Real_Math_sin rs => doMathCall ("sin", rs)
             | Real_Math_sqrt rs => doMathCall ("sqrt", rs)
             (*
             | Real_Math_tan _ => false
             *)
             | Real_abs rs => doMathCall ("fabs", rs)
             | Real_add _ => doBinAL "fadd"
             | Real_castToWord (_, ws) => doConv ("bitcast", "%Word" ^ (WordSize.toString ws))
             | Real_div _ => doBinAL "fdiv"
             | Real_equal _ => doCmp "fcmp oeq"
             (*
             | Real_ldexp _ => false
             *)
             | Real_le _ => doCmp "fcmp ole"
             | Real_lt _ => doCmp "fcmp olt"
             | Real_mul _ => doBinAL "fmul"
             | Real_muladd rs => doMathCall ("fma", rs)
             | Real_mulsub rs =>
                  let
                     val tmp = emitPrimApp {args = Vector.new1 (arg 2), prim = Prim.realNeg rs}
                     val res = emitPrimApp {args = Vector.new3 (arg 0, arg 1, tmp), prim = Prim.realMulAdd rs}
                  in
                     res
                  end
             | Real_neg rs => emitPrimApp {args = Vector.new2 ((argTy 0, "-0.0"), arg 0), prim = Prim.realSub rs}
             | Real_qequal _ => doCmp "fcmp ueq"
             | Real_rndToReal (rs1, rs2) =>
                  let
                     val conv =
                        case RealSize.compare (rs1, rs2) of
                           LESS => "fpext"
                         | EQUAL => "bitcast"
                         | GREATER => "fptrunc"
                  in
                     doConv (conv, "%Real" ^ (RealSize.toString rs2))
                  end
             | Real_rndToWord (rs, ws, {signed}) =>
                  let
                     val conv = if signed then "fptosi" else "fptoui"
                  in
                     doConv (conv, "%Word" ^ (WordSize.toString ws))
                  end
             | Real_round rs => doMathCall ("rint", rs)
             | Real_sub _ => doBinAL "fsub"
             (*
             | Thread_returnToC => false
             *)
             | Word_add _ => doBinAL "add"
             | Word_addCheck (ws, {signed}) => doCheckCall (if signed then "sadd" else "uadd", ws)
             | Word_andb _ => doBinAL "and"
             | Word_castToReal (ws, rs) => doConv ("bitcast", "%Real" ^ (RealSize.toString rs))
             | Word_equal _ => doCmp "icmp eq"
             | Word_extdToWord (ws1, ws2, {signed}) =>
                  let
                     val conv =
                        case WordSize.compare (ws1, ws2) of
                           LESS => if signed then "sext" else "zext"
                         | EQUAL => "bitcast"
                         | GREATER => "trunc"
                  in
                     doConv (conv, "%Word" ^ (WordSize.toString ws2))
                  end
             | Word_lshift ws =>
                  let
                     val arg1 = emitPrimApp {args = Vector.new1 (arg 1), prim = Prim.wordExtdToWord (WordSize.shiftArg, ws, {signed = false})}
                     val resTy = argTy 0
                     val res = LLVM.Reg.tmp ()
                     val () = print (mkinst (res, "shl", resTy, argReg 0, #2 arg1))
                  in
                     (resTy, res)
                  end
             | Word_lt (_, {signed}) => doCmp (if signed then "icmp slt" else "icmp ult")
             | Word_mul _ => doBinAL "mul"
             | Word_mulCheck (ws, {signed}) => doCheckCall (if signed then "smul" else "umul", ws)
             | Word_neg ws => emitPrimApp {args = Vector.new2 ((argTy 0, "0"), arg 0), prim = Prim.wordSub ws}
             | Word_negCheck ws => emitPrimApp {args = Vector.new2 ((argTy 0, "0"), arg 0), prim = Prim.wordSubCheck (ws, {signed = true})}
             | Word_notb ws => emitPrimApp {args = Vector.new2 ((argTy 0, "-1"), arg 0), prim = Prim.wordXorb ws}
             | Word_orb _ => doBinAL "or"
             | Word_quot (_, {signed}) => doBinAL (if signed then "sdiv" else "udiv")
             | Word_rem (_, {signed}) => doBinAL (if signed then "srem" else "urem")
             | Word_rndToReal (ws, rs, {signed}) => doConv (if signed then "sitofp" else "uitofp", "%Real" ^ (RealSize.toString rs))
             | Word_rol ws =>
                  let
                     (* (arg0 >> (size - arg1)) | (arg0 << arg1) *)
                     val tmpA = emitPrimApp {args = Vector.new2 ((argTy 1, WordSize.toString ws), arg 1), prim = Prim.wordSub WordSize.shiftArg}
                     val tmpB = emitPrimApp {args = Vector.new2 (arg 0, tmpA), prim = Prim.wordRshift (ws, {signed = false})}
                     val tmpC = emitPrimApp {args = Vector.new2 (arg 0, arg 1), prim = Prim.wordLshift ws}
                     val res = emitPrimApp {args = Vector.new2 (tmpB, tmpC), prim = Prim.wordOrb ws}
                  in
                     res
                  end
             | Word_ror ws =>
                  let
                     (* (arg0 >> arg1) | (arg0 << (size - arg1)) *)
                     val tmpA = emitPrimApp {args = Vector.new2 (arg 0, arg 1), prim = Prim.wordRshift (ws, {signed = false})}

                     val tmpB = emitPrimApp {args = Vector.new2 ((argTy 1, WordSize.toString ws), arg 1), prim = Prim.wordSub WordSize.shiftArg}
                     val tmpC = emitPrimApp {args = Vector.new2 (arg 0, tmpB), prim = Prim.wordLshift ws}
                     val res = emitPrimApp {args = Vector.new2 (tmpA, tmpC), prim = Prim.wordOrb ws}
                  in
                     res
                  end
             | Word_rshift (ws, {signed}) =>
                  let
                     val arg1 = emitPrimApp {args = Vector.new1 (arg 1), prim = Prim.wordExtdToWord (WordSize.shiftArg, ws, {signed = false})}
                     val resTy = argTy 0
                     val res = LLVM.Reg.tmp ()
                     val () = print (mkinst (res, if signed then "ashr" else "lshr", resTy, argReg 0, #2 arg1))
                  in
                     (resTy, res)
                  end
             | Word_sub _ => doBinAL "sub"
             | Word_subCheck (ws, {signed}) => doCheckCall (if signed then "ssub" else "usub", ws)
             | Word_xorb _ => doBinAL "xor"
             | _ => Error.bug ("LLVMCodegen.emitChunk.emitPrimApp" ^ (Prim.toString prim))
         end

      fun emitStatement statement =
         let
            val () =
               if !Control.Native.commented > 1
                  then prints ["\t; ", Layout.toString (Statement.layout statement), "\n"]
               else ()
         in
            case statement of
               Statement.Move {dst, src} =>
                  let
                     val (_, srcReg) = operandToValue src
                     val (dstTy, dstReg) = operandToAddr dst
                     val () = print (mkstore (dstTy, srcReg, dstReg))
                  in
                     ()
                  end
             | Statement.Noop => print "\t; Noop\n"
             | Statement.PrimApp {args, dst, prim} =>
                  let
                     val args = Vector.map (args, operandToValue)
                     val (_, resReg) = emitPrimApp {args = args, prim = prim}
                     val () =
                        Option.app
                        (dst, fn dst =>
                         let
                            val (dstTy, dstReg) = operandToAddr dst
                         in
                            print (mkstore (dstTy, resReg, dstReg))
                         end)
                  in
                     ()
                  end
             | Statement.ProfileLabel _ =>
                  Error.bug "LLVMCodegen.emitChunk.emitStatement: ProfileLabel"
         end

      fun emitTransfer transfer =
         let
            val () =
               if !Control.Native.commented > 1
                  then prints ["\t; ", Layout.toString (Transfer.layout transfer), "\n"]
               else ()
            fun push (return: Label.t, size: Bytes.t) =
               let
                  val () =
                     (emitStatement o Statement.Move)
                     {dst = Operand.stackOffset
                            {offset = Bytes.- (size, Runtime.labelSize ()),
                             ty = Type.label return},
                      src = Operand.Label return}
                  val () = print (stackPush (llbytes size))
                  val () =
                     if !Control.profile = Control.ProfileTimeField
                        then print (flushStackTop ())
                     else ()
               in
                  ()
               end
            fun doNextViaLabel dstLabel =
               let
                  val dstChunkLabel = labelChunk dstLabel
                  val () =
                     if ChunkLabel.equals (chunkLabel, dstChunkLabel)
                        then prints ["\tbr label%", Label.toString dstLabel, "\n"]
                     else let
                             val () = print "\t;doNextViaLabel\n"
                             (* cont.nextChunk = ChunkN *)
                             val dstChunkName = "@Chunk" ^ chunkLabelToString dstChunkLabel
                             val () = addCFunction (concat ["%struct.cont ", dstChunkName, "()"])
                             val dstChunkPtrReg = LLVM.Reg.tmp ()
                             val () = print (mkconv (dstChunkPtrReg, "bitcast", "%struct.cont ()*", dstChunkName, "i8*"))
                             val nextChunkPtrReg = LLVM.Reg.tmp ()
                             val () = print (mkgep (nextChunkPtrReg, "%struct.cont*", "%cont", [("i32", "0"), ("i32", "0")]))
                             val () = print (mkstore ("i8*", dstChunkPtrReg, nextChunkPtrReg))
                             (* nextFun = l *)
                             val () = print (mkstore ("%uintptr_t", labelToStringIndex dstLabel, "%l_nextFun"))
                             val () = print "\tbr label %exit\n"
                          in
                             ()
                          end
               in
                  ()
               end
            fun doNextViaStackTop () =
               let

                  val () = print "\t;doNextViaStackTop\n"
                  (* l_nextFun = *(( uintptr_t* )(StackTop - sizeof( void* ))); *)
                  val stackTop = LLVM.Reg.tmp ()
                  val () = print (mkload (stackTop, "%Pointer*", "%stackTop"))
                  val stackTopOffset = LLVM.Reg.tmp ()
                  val offset = (llbytes o Bits.toBytes o Control.Target.Size.cpointer) ()
                  val () = print (mkgep (stackTopOffset, "%Pointer", stackTop, [("i32", "-" ^ offset)]))
                  val stackTopOffsetCast = LLVM.Reg.tmp ()
                  val () = print (mkconv (stackTopOffsetCast, "bitcast", "%Pointer", stackTopOffset, "%uintptr_t*"))
                  val nextFun = LLVM.Reg.tmp ()
                  val () = print (mkload (nextFun, "%uintptr_t*", stackTopOffsetCast))
                  val () = print (mkstore ("%uintptr_t", nextFun, "%l_nextFun"))
                  (* goto top; *)
                  val () = print "\tbr label %top\n"
               in
                  ()
               end
         in
            case transfer of
               Transfer.Arith {args, dst, overflow, prim, success} =>
                  let
                     val () = print "\t;arithmetic transfer\n"
                     val args = Vector.map (args, operandToValue)
                     val (ty, res_obit) = emitPrimApp {args = args, prim = prim}
                     val resReg = LLVM.Reg.tmp ()
                     val () = prints ["\t", resReg, " = extractvalue ", ty, " ", res_obit, ", 0\n"]
                     val obitReg = LLVM.Reg.tmp ()
                     val () = prints ["\t", obitReg, " = extractvalue ", ty, " ", res_obit, ", 1\n"]
                     val (dstTy, dstReg) = operandToAddr dst
                     val () = print (mkstore (dstTy, resReg, dstReg))
                     val () = prints ["\tbr i1 ", obitReg, ", ",
                                      "label %", Label.toString overflow, ", ",
                                      "label %", Label.toString success, "\n"]
                  in
                     ()
                  end
             | Transfer.CCall {args, frameInfo, func, return} =>
                  let
                     val () = print (outputTransfer (context, transfer, chunkLabel))
                  in
                     ()
                  end
             | Transfer.Call {label, return, ...} =>
                  let
                     val () =
                        Option.app
                        (return, fn {return, size, ...} =>
                         push (return, size))
                     val () = doNextViaLabel label
                  in
                     ()
                  end
             | Transfer.Goto label =>
                  prints ["\tbr label %", Label.toString label, "\n"]
             | Transfer.Raise =>
                  let
                     (* StackTop = StackBottom + ExnStack *)
                     val (sbpre, stackBottomAddr) = offsetGCState (GCField.StackBottom, "%Pointer*")
                     val () = print sbpre
                     val stackBottom = LLVM.Reg.tmp ()
                     val () = print (mkload (stackBottom, "%Pointer*", stackBottomAddr))
                     val (espre, exnStackAddr) = offsetGCState (GCField.ExnStack, "i32*")
                     val () = print espre
                     val exnStack = LLVM.Reg.tmp ()
                     val loadExnStack = mkload (exnStack, "i32*", exnStackAddr)
                     val stackBottomPlusExnStack = LLVM.Reg.tmp ()
                     val gep = mkgep (stackBottomPlusExnStack, "%Pointer", stackBottom, [("i32", exnStack)])
                     val store = mkstore ("%Pointer", stackBottomPlusExnStack, "%stackTop")

                     val () = doNextViaStackTop ()
                  in
                     ()
                  end
             | Transfer.Return =>
                  let
                     val () = doNextViaStackTop ()
                  in
                     ()
                  end
             | Transfer.Switch (Switch.T {cases, default, test, ...}) =>
                  let
                     val (testTy, testReg) = operandToValue test
                     val defaultLabel =
                        case default of
                           NONE => unreachableLabel
                         | SOME l => l
                     val () = prints ["\tswitch ", testTy, " ", testReg, ", "]
                     val () = prints ["label %", Label.toString defaultLabel, "\n"]
                     val () = print "\t\t[\n"
                     val () =
                        Vector.foreach
                        (cases, fn (w, l) =>
                         prints ["\t\t\t", testTy, " ", llwordx w, ", label %", Label.toString l, "\n"])
                     val () = print "\t\t]\n"
                  in
                     ()
                  end
         end

      fun emitBlock block =
         let
            val Block.T {kind, label, statements, transfer, ...} = block

            val () = print "\n"
            val () = prints [Label.toString label, ":\n"]

            fun pop fi = print ((stackPush o llbytes o Bytes.~ o Program.frameSize) (program, fi))
            val () =
               case kind of
                  Kind.Cont {frameInfo, ...} => pop frameInfo
                | Kind.CReturn {dst, frameInfo, ...} =>
                     let
                        val () = Option.app (frameInfo, pop)
                        val () =
                           Option.app
                           (dst, fn x =>
                            let
                               val x = Live.toOperand x
                               val ty = Operand.ty x
                               val llvmTy = llty ty
                               val reg = LLVM.Reg.tmp ()
                               val load = mkload (reg, llvmTy ^ "*", "@CReturn" ^ CType.name (Type.toCType ty))
                               val (dstpre, dstty, dstreg) = getOperandAddr (context, x)
                               val store = mkstore (dstty, reg, dstreg)
                            in
                               prints [dstpre, load, store]
                            end)
                     in
                        ()
                     end
                | Kind.Handler {frameInfo, ...} => pop frameInfo
                | _ => ()

            val () = Vector.foreach (statements, emitStatement)
            val () = emitTransfer transfer
         in
            ()
         end

      val () = print "\n"
      (* C-Types *)
      val () = print "; c-types\n"
      val () = prints ["%uintptr_t = type i", WordSize.toString (WordSize.cpointer ()), "\n"]
      val () = print "\n"
      (* ML-Types *)
      val () = print "; ml-types\n"
      val () = prints ["%Pointer = type i8*\n",
                       "%Int8 = type i8\n",
                       "%Int16 = type i16\n",
                       "%Int32 = type i32\n",
                       "%Int64 = type i64\n",
                       "%Real32 = type float\n",
                       "%Real64 = type double\n",
                       "%Word8 = type i8\n",
                       "%Word16 = type i16\n",
                       "%Word32 = type i32\n",
                       "%Word64 = type i64\n",
                       "%CPointer = type i8*\n",
                       "%Objptr = type %Pointer\n",
                       "%BlockId = type %uintptr_t\n"]
      val () = print "\n"
      (* LLVM Intrinsics *)
      val () = print "; llvm intrinsics\n"
      val () = List.foreach
               (WordSize.prims, fn ws =>
                let
                   val ws = WordSize.toString ws
                   val ty = "%Word" ^ ws
                   val operTy = "i" ^ ws
                   fun emitOverflow oper =
                      prints ["declare {", ty, ", i1} ",
                              "@llvm.", oper, ".with.overflow.", operTy,
                              "(", ty, ",", ty, ")\n"]
                   val () = List.foreach (["sadd", "uadd", "ssub", "usub", "smul", "umul"], emitOverflow)
                in
                   ()
                end)
      val () = List.foreach
               (RealSize.all, fn rs =>
                let
                   val rs = RealSize.toString rs
                   val ty = "%Real" ^ rs
                   val operTy = "f" ^ rs
                   fun emitOp (oper, arity) =
                      let
                         val () = prints ["declare ", ty, " @llvm.", oper, ".", operTy, "("]
                         val () = Int.for (0, arity - 1, fn _ => prints [ty, ","])
                         val () = prints [ty, ")\n"]
                      in
                         ()
                      end
                   fun emitUnop oper = emitOp (oper, 1)
                   fun emitBinop oper = emitOp (oper, 2)
                   fun emitTernop oper = emitOp (oper, 3)
                   val () = List.foreach (["sqrt", "sin", "cos", "exp", "log", "log10", "fabs", "rint"], emitUnop)
                   val () = List.foreach (["fma"], emitTernop)
                in
                   ()
                end)
      val () = print "\n"
      (* Globals *)
      val () = print "; Globals\n"
      val () =
         List.foreach
         (CType.all, fn ty =>
          let
             val s = CType.toString ty
             val () = prints ["@global", s, " = ",
                              "external hidden global ",
                              "[", Int.toString (Global.numberOfType ty), " x %", s, "]\n"]
          in
             ()
          end)
      val () =
         prints ["@globalObjptrNonRoot = ",
                 "external hidden global ",
                 "[", Int.toString (Global.numberOfNonRoot ()), " x %Objptr]\n"]
      val () = print "\n"
      (* CReturns *)
      val () = print "; CReturns\n"
      val () =
         List.foreach
         (CType.all, fn ty =>
          let
             val () = prints ["@CReturn", CType.name ty, " = ",
                              "external hidden global ",
                              "%", CType.toString ty, "\n"]
          in
             ()
          end)
      val () = print "\n"
      (* ??? *)
      val () = print "%struct.cont = type { i8* }\n"
      val () = print "%struct.GC_state = type opaque\n"
      val () = print "@returnToC = external hidden global i32\n"
      val () = print "@nextChunks = external hidden global [0 x %struct.cont () *]\n"
      val () = print "@gcState = external hidden global %struct.GC_state\n"
      val () = print "\n"

      val () = print "\n\n"
      val () = prints ["define hidden %BlockId @Chunk", chunkLabelToString chunkLabel, " (%uintptr_t %nextBlock) {\n"]

      val () = print "\n"
      val () = print "entry:\n"
      val () = print "\t%cont = alloca %struct.cont\n"
      val () = print "\t%l_nextFun = alloca %uintptr_t\n"
      val nextFun = LLVM.Reg.tmp ()
      val () = print (mkstore ("%uintptr_t", "%nextBlock", "%l_nextFun"))
      val () = print "\t%frontier = alloca %Pointer\n"
      val () = print (cacheFrontier ())
      val () = print "\t%stackTop = alloca %Pointer\n"
      val () = print (cacheStackTop ())
      val () = List.foreach
               (CType.all, fn ty =>
                let
                   val pre = concat ["\t%reg", CType.name ty, "_"]
                   val post = concat [" = alloca %", CType.toString ty, "\n"]
                in
                   Int.for (0, 1 + regMax ty, fn i =>
                            prints [pre, Int.toString i, post])
                end)
      val () = print "\tbr label %top\n"

      val () = print "\n"
      val () = print "top:\n"
      val nextFun = LLVM.Reg.tmp ()
      val () = print (mkload (nextFun, "%uintptr_t*", "%l_nextFun"))
      val () = prints ["\tswitch %uintptr_t ", nextFun, ", label %default [\n"]
      val () = Vector.foreach
               (blocks, fn Block.T {kind, label, ...} =>
                if Kind.isEntry kind
                   then prints ["\t\t%uintptr_t ", labelToStringIndex label, ", label %", Label.toString label, "\n"]
                else ())
      val () = print "\t]\n";

      val () = Vector.foreach (blocks, emitBlock)

      val () = print "\n"
      val () = print "default:\n"
      val () = print "\tbr label %exit\n"

      val () = print "\n"
      val () = print "exit:\n"
      val () = print (flushFrontier ())
      val () = print (flushStackTop ())
      val nextFun = LLVM.Reg.tmp ()
      val () = print (mkload (nextFun, "%BlockId*", "%l_nextFun"))
      val () = prints ["\tret %BlockId ", nextFun, "\n"]

      val () = print "\n"
      val () = prints [Label.toString unreachableLabel, ":\n"]
      val () = print "\tunreachable\n"

      val () = print "\n"
      val () = print "}\n"

      val () = print "\n"
      val () = List.foreach
               (!cFunctions, fn f =>
                prints ["declare ", f, "\n"])
      val () = List.foreach
               (!ffiSymbols, fn {name, cty, symbolScope} =>
                let
                   val ty =
                      case cty of
                         SOME t => "%" ^ CType.toString t
                       | NONE => "void"
                   val visibility =
                      case symbolScope of
                         CFunction.SymbolScope.External => "default"
                       | CFunction.SymbolScope.Private => "hidden"
                       | CFunction.SymbolScope.Public => "default"
                in
                   prints ["@", name, " = external ", visibility, " global ", ty, "\n"]
                end)

      val () = done ()
   in
      ()
   end

fun makeContext program =
    let
        val Program.T { chunks, frameLayouts, ...} = program
        val {get = labelInfo: Label.t -> {chunkLabel: ChunkLabel.t,
                                          frameIndex: int option},
             set = setLabelInfo, ...} =
            Property.getSetOnce

                (Label.plist, Property.initRaise ("LLVMCodeGen.info", Label.layout))
        val entryLabels: (Label.t * int) list ref = ref []
        val indexCounter = Counter.new (Vector.length frameLayouts)
        val _ =
         List.foreach
         (chunks, fn Chunk.T {blocks, chunkLabel, ...} =>
          Vector.foreach
          (blocks, fn b as Block.T {kind, label, ...} =>
           let
              fun entry (index: int) =
                 List.push (entryLabels, (label, index))
              val frameIndex =
                 case Kind.frameInfoOpt kind of
                    NONE => (if Kind.isEntry kind
                                then entry (Counter.next indexCounter)
                             else ()
                             ; NONE)
                  | SOME (FrameInfo.T {frameLayoutsIndex, ...}) =>
                    (entry frameLayoutsIndex
                    ; SOME frameLayoutsIndex)
           in
              setLabelInfo (label, {chunkLabel = chunkLabel,
                                    frameIndex = frameIndex})
           end))
        val a = Array.fromList (!entryLabels)
        val () = QuickSort.sortArray (a, fn ((_, i), (_, i')) => i <= i')
        val entryLabels = Vector.map (Vector.fromArray a, #1)
        val labelChunk = #chunkLabel o labelInfo
        val {get = chunkLabelIndex: ChunkLabel.t -> int, ...} =
            Property.getSet (ChunkLabel.plist,
                             Property.initFun (let
                                                  val c = Counter.new 0
                                              in
                                                  fn _ => Counter.next c
                                              end))
        val chunkLabelToString = llint o chunkLabelIndex
        val {get = labelIndex, set = setLabelIndex, ...} =
            Property.getSetOnce (Label.plist,
                                 Property.initRaise ("index", Label.layout))
        val _ =
            Vector.foreachi (entryLabels, fn (i, l) => setLabelIndex (l, i))
        (* NB: This should always return the same value as
         * (Int.toString o valOf o #frameIndex o labelInfo) l
         *)
        fun labelToStringIndex (l: Label.t): string = llint (labelIndex l)
    in
        Context { program = program,
                  labelToStringIndex = labelToStringIndex,
                  chunkLabelIndex = chunkLabelIndex,
                  chunkLabelToString = chunkLabelToString,
                  labelChunk = labelChunk,
                  entryLabels = entryLabels
                }
    end

fun emitLLVM {context, outputLL} =
    let
        val Context { program, ... } = context
        val Program.T { chunks, ...} = program
        val () = List.foreach (chunks, fn chunk => emitChunk {context = context, chunk = chunk, outputLL = outputLL})
    in
        ()
    end

fun emitC {context, outputC} =
    let
        val Context { program, ... } = context
        val {print, done, file=_} = outputC ()
        val Program.T {main = main, chunks = chunks, ... } = program
        val Context { chunkLabelToString, entryLabels, labelChunk, labelToStringIndex, ... } = context
        val chunkLabel = chunkLabelToString (#chunkLabel main)
        val mainLabel = labelToStringIndex (#label main)
        val additionalMainArgs = [chunkLabel, mainLabel]
        fun declareChunk (Chunk.T {chunkLabel, ...}, print) =
            C.call ("DeclareChunk",
                    [chunkLabelToString chunkLabel],
                    print)
        fun rest () =
            (List.foreach (chunks, fn c => declareChunk (c, print))
            ; print "PRIVATE struct cont ( *nextChunks []) () = {\n"
            ; Vector.foreach (entryLabels, fn l =>
                             let
                             in
                                 print "\t"
                               ; C.callNoSemi ("Chunkp",
                                               [chunkLabelToString (labelChunk l)],
                                               print)
                               ; print ",\n"
                             end)
            ; print "};\n")
    in
        CCodegen.outputDeclarations
            {additionalMainArgs = additionalMainArgs,
             includes = ["llvm-main.h"],
             print = print,
             program = program,
             rest = rest}
      ; done ()
    end

fun output {program, outputC, outputLL} =
   let
      val context = makeContext program
      val () = emitC {context = context, outputC = outputC}
      val () = emitLLVM {context = context, outputLL = outputLL}
   in
      ()
   end
end
