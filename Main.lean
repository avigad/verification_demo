import Cli
import Demo.Demo

def main (args : List String) : IO Unit := do
  println! "Hello world"
  println! (fib' 10000)