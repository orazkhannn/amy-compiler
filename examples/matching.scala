object Patterns {
    abstract class E
    case class A()            extends E
    case class B(n: Int)      extends E
    case class C(x: Int, y: Int) extends E
  
    // test all 4 kinds of patterns
    def test(e: E): Int = {
        e match {
            case A()        => 0            // nullary‐constructor
            case B(v)       => v * 2        // single‐field
            case C(x, y)    => x + y        // two‐fields
            case _          => -1           // wildcard
        }
    }
  
    // nested pattern: a list of Es
    abstract class L
    case class Nil()            extends L
    case class Cons(h: E, t: L) extends L
  
    def sumEs(lst: L): Int = {
        lst match {
            case Nil()            => 0
            case Cons(A(),  tail) => 100 + sumEs(tail)                   // literal‐constructor in pattern
            case Cons(B(n), tail) => n + sumEs(tail)
            case Cons(C(x,y), Nil()) => x * y
            case _                => error("bad list")                   // error in match
        }
    }
  
    // print them all
    Std.printInt(test(A()));
    Std.printInt(test(B(21)));
    Std.printInt(test(C(4,5)));
    Std.printInt(test(A()));                   // default wildcard never reached
    Std.printInt(sumEs(Cons(A(), Cons(B(7), Cons(C(2,3), Nil())))))
  }
  