import Cli
import Demo.Demo

def main (args : List String) : IO Unit := do
  let n := args[0]!.toNat!
  println! (fib₄ n)