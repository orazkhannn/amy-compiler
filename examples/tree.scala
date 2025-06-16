object Trees {

    abstract class T
    case class Leaf(v: Int)       extends T
    case class Node(l: T, r: T)   extends T
    def max(a: Int, b: Int): Int = {
        if (a < b) {
            b
        }
        else {
            a
        }
    }
    def depth(t: T): Int = {
        t match {
            case Leaf(_) => 1
            case Node(l, r) => max(depth(l), depth(r)) + 1
        }
    }

  
    val tree: T = Node(Leaf(10), Node(Leaf(20), Leaf(5)));
    Std.printInt(depth(tree))
}