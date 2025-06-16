object Traps {
    def boom(x: Int): Int = {
      if (x == 0) {
        error("zero!") 
      }
      else {
        100 / x
      }
    }
    // this will print “50” then trap:
    Std.printInt(boom(2));
    boom(0)
  }