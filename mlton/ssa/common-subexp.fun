functor CommonSubexp (S: COMMON_SUBEXP_STRUCTS): COMMON_SUBEXP = 
struct

open S

open Exp Transfer

type word = Word.t

fun eliminate (program as Program.T {globals, datatypes, functions, main}) =
   let
      (* Keep track of the replacements of variables. *)
      val {get = replace: Var.t -> Var.t option, set = setReplace, ...} =
	 Property.getSetOnce (Var.plist, Property.initConst NONE)
      (* Keep track of the variable that holds the length of arrays (and
       * vectors and strings).
       *) 
      val {get = getLength: Var.t -> Var.t option, set = setLength, ...} =
	 Property.getSetOnce (Var.plist, Property.initConst NONE)
      fun canonVar x =
	 case replace x of
	    NONE => x
	  | SOME y => y
      fun canonVars xs = Vector.map (xs, canonVar)
      (* Canonicalize an Exp.
       * Replace vars with their replacements.
       * Put commutative arguments in canonical order.
       *)
      fun canon (e: Exp.t): Exp.t =
	 case e of
	    ConApp {con, args} =>
	       ConApp {con = con, args = canonVars args}
	  | Const _ => e
	  | PrimApp {prim, targs, args} =>
	       let
		  fun doit args = 
		     PrimApp {prim = prim, 
			      targs = targs,
			      args = args}
		  val args = canonVars args
		  fun arg i = Vector.sub (args, i)
		  fun canon2 () =
		     let
			val a0 = arg 0
			val a1 = arg 1
		     in
			(* What we really want is a total orderning on
			 * variables.  Since we don't have one, we just use
			 * the total ordering on hashes, which means that
			 * we may miss a few cse's but we won't be wrong.
			 *)
			if Var.hash a0 <= Var.hash a1
			   then (a0, a1)
			else (a1, a0)
		     end
		  datatype z = datatype Prim.Name.t
	       in
		  if Prim.isCommutative prim
		     then doit (Vector.new2 (canon2 ()))
		  else
		     if (case Prim.name prim of
			    IntInf_add => true
			  | IntInf_mul => true
			  | _ => false)
			then
			   let 
			      val (a0, a1) = canon2 ()
			   in doit (Vector.new3 (a0, a1, arg 2))
			   end
		     else doit args
	       end
	  | Select {tuple, offset} => Select {tuple = canonVar tuple,
					      offset = offset}
	  | Tuple xs => Tuple (canonVars xs)
	  | Var x => Var (canonVar x)
	  | _ => e

      (* Keep a hash table of canonicalized Exps that are in scope. *)
      val table: {hash: word, exp: Exp.t, var: Var.t} HashSet.t =
	 HashSet.new {hash = #hash}
      (* All of the globals are in scope, and never go out of scope. *)
      (* The hash-cons'ing of globals in ConstantPropagation ensures
       *  that each global is unique.
       *)
      val _
	= Vector.foreach
	  (globals,
	   fn Statement.T {var, exp, ...}
	    => let
		 val exp = canon exp
		 val hash = Exp.hash exp
		 val {var = var', ...}
		   = HashSet.lookupOrInsert
		     (table, hash, 
		      fn {exp = exp', ...} => Exp.equals (exp, exp'),
		      fn () => {exp = exp,
				hash = hash,
				var = valOf var})
	       in
		 ()
	       end)

      fun doitTree tree =
	 let
	    val blocks = ref []
	    fun loop (Tree.T (Block.T {args, label,
				       statements, transfer},
			      children)): unit =
	       let
		  val removes = ref []
		  val statements =
		     Vector.keepAllMap
		     (statements,
		      fn Statement.T {var, ty, exp} =>
		      let
			 val exp = canon exp
			 fun keep () = SOME (Statement.T {var = var,
							  ty = ty,
							  exp = exp})
		      in
			 case var of
			    NONE => keep ()
			  | SOME var => 
			       let
				  fun replace var' = (setReplace (var, SOME var');
						      NONE)
				  fun lookup () =
				     let
				        val hash = Exp.hash exp
					val {var = var', ...} =
					   HashSet.lookupOrInsert
					   (table, hash, fn {exp = exp', ...} =>
					    Exp.equals (exp, exp'),
					    fn () => {exp = exp,
						      hash = hash,
						      var = var})
				     in
				        if Var.equals (var, var')
					  then (List.push(removes, (var, hash));
						keep ())
					  else replace var'
				     end
			       in
				  case exp of
				     PrimApp (pa as {prim, args, ...}) =>
				        let
					   fun arg () = Vector.sub (args, 0)
					   fun knownLength var' =
					      let
						 val _ = setLength (var, SOME var')
					      in
						 keep ()
					      end
					   fun conv () =
					      case getLength (arg ()) of
						 NONE => keep ()
					       | SOME var' => knownLength var'
					   fun length () =
					      case getLength (arg ()) of
						 NONE => lookup ()
					       | SOME var' => replace var'
					   datatype z = datatype Prim.Name.t
					in
					   case Prim.name prim of
					      Array_array => knownLength (arg ())
					    | Array_length => length ()
					    | Vector_fromArray => conv ()
					    | String_fromCharVector => conv ()
					    | String_fromWord8Vector => conv ()
					    | String_toCharVector => conv ()
					    | String_toWord8Vector => conv ()
					    | String_size => length ()
					    | Vector_length => length ()
					    | _ => if Prim.isFunctional prim
						      orelse Prim.mayOverflow prim
						      then lookup ()
						   else keep ()
					end
				   | _ => lookup ()
			       end
		      end)
		  val transfer = Transfer.replaceVar (transfer, canonVar)
		  val block = Block.T {args = args,
				       label = label,
				       statements = statements,
				       transfer = transfer}
	       in
		  List.push (blocks, block) ;
		  Vector.foreach (children, loop) ;
		  List.foreach 
		  (!removes, fn (var, hash) =>
		   HashSet.remove
		   (table, hash, fn {var = var', ...} =>
		    Var.equals (var, var')))
	       end
	    val _ = loop tree
	 in
	    Vector.fromListRev (!blocks)
	 end

(*      val shrink = shrinkBlocks globals *)
      val functions =
	 List.map
	 (functions, fn f => 
	  let
	     val {name, args, start, blocks, returns} = Function.dest f
	     val blocks = (* shrink *) doitTree (Function.dominatorTree f)
	     val _ = Function.clear f
	  in
	     Function.new {name = name,
			   args = args,
			   start = start,
			   blocks = blocks,
			   returns = returns}
	  end)
      val program = 
	 Program.T {datatypes = datatypes,
		    globals = globals,
		    functions = functions,
		    main = main}
   in
      program
   end


end
