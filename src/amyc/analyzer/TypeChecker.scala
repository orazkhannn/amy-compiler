package amyc
package analyzer

import utils._
import ast.SymbolicTreeModule._
import ast.Identifier

// btemirov file last
// The type checker for Amy
// Takes a symbolic program and rejects it if it does not follow the Amy typing rules.
object TypeChecker extends Pipeline[(Program, SymbolTable), (Program, SymbolTable)] {

  def run(ctx: Context)(v: (Program, SymbolTable)): (Program, SymbolTable) = {
    import ctx.reporter._

    val (program, table) = v

    case class Constraint(found: TypeOrVar, expected: TypeOrVar, pos: Position)

    type TypeOrVar = Type | TypeVariable

    // Represents a type variable.
    // It is meant only for internal type checker use,
    // since no Amy value can have such type.
    case class TypeVariable private (id: Int)
    object TypeVariable {
      private val c = new UniqueCounter[Unit]
      def fresh(): TypeVariable = TypeVariable(c.next(()))
    }

    // Generates typing constraints for an expression `e` with a given expected type.
    // The environment `env` contains all currently available bindings (you will have to
    //  extend these, e.g., to account for local variables).
    // Returns a list of constraints among types. These will later be solved via unification.
    def genConstraints(e: Expr, expected: TypeOrVar)(implicit env: Map[Identifier, TypeOrVar]): List[Constraint] = {
      
      // This helper returns a list of a single constraint recording the type
      //  that we found (or generated) for the current expression `e`
      def topLevelConstraint(found: TypeOrVar): List[Constraint] =
        List(Constraint(found, expected, e.position))
      
      e match {
        case IntLiteral(_) => topLevelConstraint(IntType)
        case BooleanLiteral(_) => topLevelConstraint(BooleanType)
        case UnitLiteral() => topLevelConstraint(UnitType)
        case StringLiteral(_) => topLevelConstraint(StringType)
        
        case Equals(lhs, rhs) =>
          // HINT: Take care to implement the specified Amy semantics
          // TODO
          val leftExp = TypeVariable.fresh()
          val rightExp = TypeVariable.fresh()

          val leftConstraints = genConstraints(lhs, leftExp)(env)
          val rightConstraint = genConstraints(rhs, rightExp)(env)

          val equalityConstraint = Constraint(leftExp, rightExp, e.position)
          val resultConstraint = Constraint(BooleanType, expected, e.position)

          leftConstraints ++ rightConstraint ++ List(equalityConstraint, resultConstraint)

        case Plus(lhs, rhs) =>
          val leftConstraints = genConstraints(lhs, IntType)(env)
          val rightConstraint = genConstraints(rhs, IntType)(env)

          leftConstraints ++ rightConstraint ++ topLevelConstraint(IntType)

        case Minus(lhs, rhs) =>
          val leftConstraints = genConstraints(lhs, IntType)(env)
          val rightConstraint = genConstraints(rhs, IntType)(env)

          leftConstraints ++ rightConstraint ++ topLevelConstraint(IntType)
        
        case Times(lhs, rhs) =>
          val leftConstraints = genConstraints(lhs, IntType)(env)
          val rightConstraint = genConstraints(rhs, IntType)(env)

          leftConstraints ++ rightConstraint ++ topLevelConstraint(IntType)

        case Div(lhs, rhs) => 
          val leftConstraints = genConstraints(lhs, IntType)(env)
          val rightConstraint = genConstraints(rhs, IntType)(env)

          leftConstraints ++ rightConstraint ++ topLevelConstraint(IntType)

        case Mod(lhs, rhs) =>
          val leftConstraints = genConstraints(lhs, IntType)(env)
          val rightConstraint = genConstraints(rhs, IntType)(env)

          leftConstraints ++ rightConstraint ++ topLevelConstraint(IntType)

        case LessThan(lhs, rhs) =>
          val leftConstraints = genConstraints(lhs, IntType)(env)
          val rightConstraint = genConstraints(rhs, IntType)(env)

          leftConstraints ++ rightConstraint ++ topLevelConstraint(BooleanType)
        
        case LessEquals(lhs, rhs) =>
          val leftConstraints = genConstraints(lhs, IntType)(env)
          val rightConstraint = genConstraints(rhs, IntType)(env)

          leftConstraints ++ rightConstraint ++ topLevelConstraint(BooleanType)

        case And(lhs, rhs) =>
          val leftConstraints = genConstraints(lhs, BooleanType)(env)
          val rightConstraint = genConstraints(rhs, BooleanType)(env)

          leftConstraints ++ rightConstraint ++ topLevelConstraint(BooleanType)

        case Or(lhs, rhs) =>
          val leftConstraints = genConstraints(lhs, BooleanType)(env)
          val rightConstraint = genConstraints(rhs, BooleanType)(env)

          leftConstraints ++ rightConstraint ++ topLevelConstraint(BooleanType)

        case Concat(lhs, rhs) =>
          val leftConstraints = genConstraints(lhs, StringType)(env)
          val rightConstraint = genConstraints(rhs, StringType)(env)

          leftConstraints ++ rightConstraint ++ topLevelConstraint(StringType)

        case Not(e) =>
          val constraints = genConstraints(e, BooleanType)(env)
          constraints ++ topLevelConstraint(BooleanType)
        
        case Neg(e) =>
          val constraints = genConstraints(e, IntType)(env)
          constraints ++ topLevelConstraint(IntType)

        case Call(qname, args) =>
          table.getConstructor(qname) match {
            case Some(sig) =>
              val paramTypes = sig.argTypes
              val returnType = sig.retType

              if (args.length != paramTypes.length) {
                ctx.reporter.error(s"Incorrect number of arguments for $qname", e.position)
                List()
              } 
              else {
                val argConstraints = args.zip(paramTypes).flatMap { 
                  case (arg, paramType) => genConstraints(arg, paramType)(env)
                }

                argConstraints ++ topLevelConstraint(returnType)
              }

            case None =>
              table.getFunction(qname) match {
                case Some(sig) =>
                  val paramTypes = sig.argTypes
                  val returnType = sig.retType

                  if (args.length != paramTypes.length) {
                    ctx.reporter.error(s"Incorrect number of arguments for $qname", e.position)
                    List()
                  } 
                  else {
                    val argConstraints = args.zip(paramTypes).flatMap { 
                      case (arg, paramType) => genConstraints(arg, paramType)(env)
                    }

                    argConstraints ++ topLevelConstraint(returnType)
                  }
                case None =>
                  ctx.reporter.error(s"Function or Constructor $qname not found", e.position)
                  List()
              }
          }

        case Sequence(e1, e2) =>
          val firstType = TypeVariable.fresh()
          val secondType = TypeVariable.fresh()

          val firstConstraints = genConstraints(e1, firstType)(env)
          val secondConstraints = genConstraints(e2, secondType)(env)

          firstConstraints ++ secondConstraints ++ topLevelConstraint(secondType)

        case Let(df, value, body) =>
          val exprConstraints = genConstraints(value, df.tt.tpe)(env)

          val bodyType = TypeVariable.fresh()
          val bodyConstraints = genConstraints(body, bodyType)(env + (df.name -> df.tt.tpe))

          exprConstraints ++ bodyConstraints ++ topLevelConstraint(bodyType)

        case Ite(cond, thenn, elze) =>
          val condConstraints = genConstraints(cond, BooleanType)(env)

          val thenConstraints = genConstraints(thenn, expected)(env)
          val elseConstraints = genConstraints(elze, expected)(env)

          condConstraints ++ thenConstraints ++ elseConstraints

        case Error(msg) =>
          val msgConstraints = genConstraints(msg, StringType)(env)
          msgConstraints ++ topLevelConstraint(expected)
        
        case Match(scrut, cases) =>
          // Returns additional constraints from within the pattern with all bindings
          // from identifiers to types for names bound in the pattern.
          // (This is analogous to `transformPattern` in NameAnalyzer.)
          def handlePattern(pat: Pattern, scrutExpected: TypeOrVar):
            (List[Constraint], Map[Identifier, Type]) =
          {
            // TODO
            pat match {
              case WildcardPattern() => (List(), Map())
              case IdPattern(name) => 
                val nameType = TypeVariable.fresh()
                (List(Constraint(nameType, scrutExpected, pat.position)), Map(name -> scrutExpected.asInstanceOf[Type]))
              case LiteralPattern(lit) =>
                lit match {
                  case IntLiteral(_) => (List(Constraint(IntType, scrutExpected, pat.position)), Map())
                  case BooleanLiteral(_) => (List(Constraint(BooleanType, scrutExpected, pat.position)), Map())
                  case StringLiteral(_) => (List(Constraint(StringType, scrutExpected, pat.position)), Map())
                  case UnitLiteral() => (List(Constraint(UnitType, scrutExpected, pat.position)), Map())
                }
              case CaseClassPattern(constr, args) =>
                table.getConstructor(constr) match {
                  case Some(sig) =>
                    val paramTypes = sig.argTypes
                    val returnType = sig.retType

                    if (args.length != paramTypes.length) {
                      ctx.reporter.error(s"Incorrect number of arguments for $constr", e.position)
                      (List(), Map())
                    }
                    else {
                      val retConstraint = List(Constraint(returnType, scrutExpected, pat.position))
                      val (argConstraints, argBindings) = args.zip(paramTypes).map {
                        case (arg, paramType) => handlePattern(arg, paramType)
                      }.unzip

                      (retConstraint ++ argConstraints.flatten, argBindings.flatten.toMap)
                    }
                  case None => 
                    ctx.reporter.error(s"Constructor $constr not found", pat.position)
                    (List(), Map())
                }
            }
          }

          def handleCase(cse: MatchCase, scrutExpected: TypeOrVar): List[Constraint] = {
            val (patConstraints, moreEnv) = handlePattern(cse.pat, scrutExpected)
            val exprConstraints = genConstraints(cse.expr, expected)(env ++ moreEnv)
            patConstraints ++ exprConstraints
          }

          val st = TypeVariable.fresh()
          genConstraints(scrut, st) ++ cases.flatMap(cse => handleCase(cse, st))

        // TODO: Implement the remaining cases        
        case Variable(name) => 
          env.get(name) match {
            case Some(tpe) => topLevelConstraint(tpe)
            case None =>
              ctx.reporter.error(s"Variable $name not found", e.position)
              List()
          }
      }
    }


    // Given a list of constraints `constraints`, replace every occurence of type variable
    //  with id `from` by type `to`.
    def subst_*(constraints: List[Constraint], from: Int, to: TypeOrVar): List[Constraint] = {
      // Do a single substitution.
      def subst(tpe: TypeOrVar, from: Int, to: TypeOrVar): TypeOrVar = {
        tpe match {
          case TypeVariable(`from`) => to
          case other => other
        }
      }

      constraints map { case Constraint(found, expected, pos) =>
        Constraint(subst(found, from, to), subst(expected, from, to), pos)
      }
    }

    // Solve the given set of typing constraints and report errors
    //  using `ctx.reporter.error` if they are not satisfiable.
    // We consider a set of constraints to be satisfiable exactly if they unify.
    def solveConstraints(constraints: List[Constraint]): Unit = {
      constraints match {
        case Nil => ()
        case Constraint(found, expected, pos) :: more =>
          // HINT: You can use the `subst_*` helper above to replace a type variable
          //       by another type in your current set of constraints.
          (found, expected) match {
            case (TypeVariable(id1), TypeVariable(id2)) => 
              if (id1 == id2) { solveConstraints(more) }
              else {
                solveConstraints(subst_*(more, id1, expected))
              }
            case (_, TypeVariable(id2)) =>
              solveConstraints(subst_*(more, id2, found))
            case (TypeVariable(_), _) =>
              solveConstraints(Constraint(expected, found, pos) :: more)
            case (type1: Type, type2: Type) => 
              if (type1 == type2) {
                solveConstraints(more)
              }
              else {
                ctx.reporter.error(s"Type mismatch: $found is not compatible with $expected", pos)
                solveConstraints(more)
              }
          }
      }
    }

    // Putting it all together to type-check each module's functions and main expression.
    program.modules.foreach { mod =>
      // Put function parameters to the symbol table, then typecheck them against the return type
      mod.defs.collect { case FunDef(_, params, retType, body) =>
        val env = params.map{ case ParamDef(name, tt) => name -> tt.tpe }.toMap
        solveConstraints(genConstraints(body, retType.tpe)(env))
      }

      // Type-check expression if present. We allow the result to be of an arbitrary type by
      // passing a fresh (and therefore unconstrained) type variable as the expected type.
      val tv = TypeVariable.fresh()
      mod.optExpr.foreach(e => solveConstraints(genConstraints(e, tv)(Map())))
    }

    v

  }
}