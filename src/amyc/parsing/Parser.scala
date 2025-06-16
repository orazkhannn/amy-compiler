package amyc
package parsing

import scala.language.implicitConversions

import amyc.ast.NominalTreeModule._
import amyc.utils._
import Token._
import TokenKind._

import scallion._
import javax.lang.model.element.QualifiedNameable
import java.lang.reflect.WildcardType

// The parser for Amy
object Parser extends Pipeline[Iterator[Token], Program]
                 with Parsers {

  type Token = amyc.parsing.Token
  type Kind = amyc.parsing.TokenKind

  import Implicits._

  override def getKind(token: Token): TokenKind = TokenKind.of(token)

  val eof: Syntax[Token] = elem(EOFKind)
  def op(string: String): Syntax[String] = accept(OperatorKind(string)) { case OperatorToken(name) => name }
  def kw(string: String): Syntax[Token] = elem(KeywordKind(string))

  implicit def delimiter(string: String): Syntax[Token] = elem(DelimiterKind(string))

  // An entire program (the starting rule for any Amy file).
  lazy val program: Syntax[Program] = many1(many1(module) ~<~ eof).map(ms => Program(ms.flatten.toList).setPos(ms.head.head))

  // A module (i.e., a collection of definitions and an initializer expression)
  lazy val module: Syntax[ModuleDef] = (kw("object") ~ identifier ~ "{" ~ many(definition) ~ opt(expr) ~ "}").map {
    case obj ~ id ~ _ ~ defs ~ body ~ _ => ModuleDef(id, defs.toList, body).setPos(obj)
  }

  // An identifier.
  val identifier: Syntax[String] = accept(IdentifierKind) {
    case IdentifierToken(name) => name
  }

  // An identifier along with its position.
  val identifierPos: Syntax[(String, Position)] = accept(IdentifierKind) {
    case id@IdentifierToken(name) => (name, id.position)
  }

  // A definition within a module.
  lazy val definition: Syntax[ClassOrFunDef] = abstractClassDef | caseClassDef | funDef

  lazy val abstractClassDef: Syntax[ClassOrFunDef] =
    (kw("abstract") ~ kw("class") ~ identifier).map {
      case kw1 ~ kw2 ~ id => AbstractClassDef(id).setPos(kw1)
    }

  lazy val caseClassDef: Syntax[ClassOrFunDef] =
    (kw("case") ~ kw("class") ~ identifier ~ "(" ~ parameters ~ ")" ~ kw("extends") ~ identifier).map {
      case kw1 ~ kw2 ~ id1 ~ _ ~ p ~ _ ~ kw3 ~ id2 => CaseClassDef(id1, p.map(t => t.tt), id2).setPos(kw1)
    }

  lazy val funDef: Syntax[ClassOrFunDef] =
    (kw("def") ~ identifier ~ "(" ~ parameters ~ ")" ~ ":" ~ typeTree ~ "=" ~ "{" ~ expr ~ "}").map {
      case kw1 ~ id1 ~ _ ~ p ~ _ ~ _ ~ t ~ _ ~ _ ~ expr ~ _ => FunDef(id1, p, t, expr).setPos(kw1)
    }

  // A list of parameter definitions.
  lazy val parameters: Syntax[List[ParamDef]] = repsep(parameter, ",").map(_.toList)

  // A parameter definition, i.e., an identifier along with the expected type.
  lazy val parameter: Syntax[ParamDef] = 
    (identifierPos ~ ":" ~ typeTree).map {
      case id ~ _ ~ t => ParamDef(id._1, t).setPos(id._2)
    }

  // A type expression.
  lazy val typeTree: Syntax[TypeTree] = primitiveType | identifierType

  // A built-in type (such as `Int`).
  val primitiveType: Syntax[TypeTree] = accept(PrimTypeKind) {
    case tk@PrimTypeToken(name) => TypeTree(name match {
      case "Unit" => UnitType
      case "Boolean" => BooleanType
      case "Int" => IntType
      case "String" => StringType
      case _ => throw new java.lang.Error("Unexpected primitive type name: " + name)
    }).setPos(tk)
  }

  // A user-defined type (such as `List`).
  lazy val identifierType: Syntax[TypeTree] = 
    (identifier ~ opt("." ~ identifier)).map {
      case id1 ~ None => TypeTree(ClassType(QualifiedName(None, id1)))
      case id1 ~ Some(_ ~ id2) => TypeTree(ClassType(QualifiedName(Some(id1), id2)))
    }


  // An expression.
  // HINT: You can use `operators` to take care of associativity and precedence
  lazy val expr: Syntax[Expr] = recursive { 
    (kw("val") ~ parameter ~ "=" ~ matchExpr ~ ";" ~ expr).map {
      case kw1 ~ p ~ _ ~ expr1 ~ _ ~ expr2 => Let(p, expr1, expr2).setPos(kw1)
    } |
    (matchExpr ~ opt(";" ~ expr)).map {
      case expr1 ~ None => expr1.setPos(expr1)
      case expr1 ~ Some(_ ~ expr2) => Sequence(expr1, expr2).setPos(expr1)
    }
   }

  lazy val matchExpr: Syntax[Expr] = recursive{
    ((orExpr | ifExpr) ~ many(kw("match") ~ "{" ~ many1(matchCase).map(m => m.toList) ~ "}").map(m => m.toList)).map {
      case expr ~ mc => mc.foldLeft(expr) {
        case (expr, kw1 ~ _ ~ mc ~_) => Match(expr, mc).setPos(kw1)
      }
    }
  }

  lazy val ifExpr: Syntax[Expr] = recursive{
    (kw("if") ~ "(" ~ expr ~ ")" ~ "{" ~ expr ~ "}" ~ kw("else") ~ "{" ~ expr ~ "}").map {
      case kw1 ~ _ ~ expr1 ~ _ ~ _ ~ expr2 ~ _ ~ kw2 ~ _ ~ expr3 ~ _ => Ite(expr1, expr2, expr3).setPos(kw1)
    }
  }

  lazy val matchCase: Syntax[MatchCase] =
    (kw("case") ~ pattern ~ delimiter("=>") ~ expr).map {
      case kw1 ~ p ~ DelimiterToken("=>") ~ expr => MatchCase(p, expr).setPos(kw1)
    }
    

  lazy val orExpr: Syntax[Expr] = recursive {
    operators(andExpr)(
      op("||") is LeftAssociative
    ){
      case (l, op, r) => Or(l,r).setPos(l)
    }
  }

  lazy val andExpr: Syntax[Expr] = recursive {
    operators(equalsExpr)(
      op("&&") is LeftAssociative
    ){
      case (l, op, r) => And(l,r).setPos(l)
    }
  }

  lazy val equalsExpr: Syntax[Expr] = recursive {
    operators(lessExpr)(
      op("==") is LeftAssociative
    ){
      case (l, op, r) => Equals(l,r).setPos(l)
    }
  }

  lazy val lessExpr: Syntax[Expr] = recursive {
    operators(plusExpr)(
      op("<") | op("<=") is LeftAssociative
    ){
      case (l, "<", r) => LessThan(l,r).setPos(l)
      case (l, "<=", r) => LessEquals(l,r).setPos(l)
    }
  }

  lazy val plusExpr: Syntax[Expr] = recursive {
    operators(timesExpr)(
      op("+") | op("-") | op("++") is LeftAssociative
    ){
      case (l, "+", r) => Plus(l,r).setPos(l)
      case (l, "-", r) => Minus(l,r).setPos(l)
      case (l, "++", r) => Concat(l,r).setPos(l)
    }
  }

  lazy val timesExpr: Syntax[Expr] = recursive {
    operators(unExpr)(
      op("*") | op("/") | op("%") is LeftAssociative
    ){
      case (l, "*", r) => Times(l,r).setPos(l)
      case (l, "/", r) => Div(l,r).setPos(l)
      case (l, "%", r) => Mod(l,r).setPos(l)
    }
  }

  lazy val unExpr: Syntax[Expr] = simpleExpr |
    (op("-") ~ simpleExpr).map {case _ ~ expr => Neg(expr).setPos(expr)} |
    (op("!") ~ simpleExpr).map {case _ ~ expr => Not(expr).setPos(expr)}

  

  // A literal expression.
  lazy val literal: Syntax[Literal[_]] =
    accept(LiteralKind) {
      case BoolLitToken(b)    => BooleanLiteral(b)
      case IntLitToken(i)     => IntLiteral(i)
      case StringLitToken(s)  => StringLiteral(s)
      case _ => UnitLiteral()
    }

  lazy val unitLiteral: Syntax[Literal[_]] =
    // unitLiteral |
    accept(LiteralKind) {
      case BoolLitToken(b)    => BooleanLiteral(b)
      case IntLitToken(i)     => IntLiteral(i)
      case StringLitToken(s)  => StringLiteral(s)
    }

  // A pattern as part of a mach case.
  lazy val pattern: Syntax[Pattern] = recursive {
    literalPattern | wildPattern |
    (identifier ~ opt("." ~ identifier) ~ opt("(" ~ repsep(pattern, ",").map(m => m.toList) ~ ")")).map {
      case id ~ None ~ None => IdPattern(id)
      case id1 ~ Some(_ ~ id2) ~ Some(_ ~ args ~ _) => CaseClassPattern(QualifiedName(Some(id1), id2), args)
      case id ~ None  ~ Some(_ ~ args ~ _) => CaseClassPattern(QualifiedName(None, id), args)
    }
  }

  lazy val literalPattern: Syntax[Pattern] = unitLiteral.map(l => LiteralPattern(l)) |
  ("("~")").map {case _ ~ _ => LiteralPattern(UnitLiteral())}


  lazy val wildPattern: Syntax[Pattern] = accept(KeywordKind("_")) {
    case KeywordToken("_") => WildcardPattern()
  }


  // HINT: It is useful to have a restricted set of expressions that don't include any more operators on the outer level.
  lazy val simpleExpr: Syntax[Expr] = unitLiteral.up[Expr] | variableOrCall | 
  (kw("error") ~ "(" ~ expr ~ ")").map {case kw ~ _ ~ expr ~ _ => Error(expr)} |
  ("(" ~ opt(expr) ~ ")").map {
    case _ ~ None ~ _ => UnitLiteral()
    case _ ~ Some(expr) ~ _ => expr
  }

  lazy val variableOrCall: Syntax[Expr] = (identifierPos ~ opt(opt("." ~ identifier) ~ "(" ~ arguments ~ ")")).map {
    case id ~ None  => Variable(id._1).setPos(id._2)
    case id1 ~ Some(Some(_ ~ id2) ~ _ ~ args ~ _) => Call(QualifiedName(Some(id1._1), id2), args).setPos(id1._2)
    case id2 ~ Some(None ~ _ ~ args ~ _) => Call(QualifiedName(None, id2._1), args).setPos(id2._2)
  } 

  lazy val arguments: Syntax[List[Expr]] = (repsep(expr, ",")).map {case args => args.toList}


  // TODO: Other definitions.
  //       Feel free to decompose the rules in whatever way convenient.


  // Ensures the grammar is in LL(1)
  lazy val checkLL1: Boolean = {
    if (program.isLL1) {
      true
    } else {
      // Set `showTrails` to true to make Scallion generate some counterexamples for you.
      // Depending on your grammar, this may be very slow.
      val showTrails = false
      debug(program, showTrails)
      false
    }
  }

  override def run(ctx: Context)(tokens: Iterator[Token]): Program = {
    import ctx.reporter._
    if (!checkLL1) {
      ctx.reporter.fatal("Program grammar is not LL1!")
    }

    val parser = Parser(program)

    parser(tokens) match {
      case Parsed(result, rest) => result
      case UnexpectedEnd(rest) => fatal("Unexpected end of input.")
      case UnexpectedToken(token, rest) => fatal("Unexpected token: " + token + ", possible kinds: " + rest.first.map(_.toString).mkString(", "))
    }
  }
}
