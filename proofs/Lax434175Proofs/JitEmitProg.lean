import Mathlib.Tactic
import Lax434175Proofs.JitRaw
import Lax434175Proofs.Cost.Polytime

/-!
The IMP+ program of the word map `JitRaw.emitF`: read the numbers, check that they are those of
an instance (walking them once and storing the membership pairs in two arrays), and write the
standard word of the construction, job by job, computing the family, segment, set and element
of every job as `HRaw.slot` does.
-/

namespace Lax434175Proofs.JitEmit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.JitRaw Lax434175Proofs.JitWords
open Lax434175Proofs.Cost (forLoop run_forLoop rdG run_rdG)
open Lax434175Proofs.Sanity.Emit (writeList run_writeList)

abbrev V (x : String) : Expr := .var x
abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev div (e f : Expr) : Expr := .bin .div e f
abbrev incr (x : String) : Com := .assign x (add (V x) (.lit 1))

/-! ### The program -/

/-- Read the three header entries. -/
def hdrCom : Com :=
  .seq (rdG "a" "L" "n" (.lit 0)) (.seq (rdG "a" "L" "m" (.lit 1)) (rdG "a" "L" "k" (.lit 2)))

/-- One number of the walk: a set size, or a member stored as a pair. -/
def walkStep : Com :=
  .ite (.eq (V "rem") (.lit 0))
    (.seq (incr "jj") (.assign "rem" (.get "a" (add (V "i") (.lit 3)))))
    (.seq (.store "MJ" (V "e") (sub (V "jj") (.lit 1)))
      (.seq (.store "MI" (V "e") (.get "a" (add (V "i") (.lit 3))))
        (.seq (incr "e") (.assign "rem" (sub (V "rem") (.lit 1))))))

def walkBody : Com := .seq walkStep (incr "i")

/-- The walk over the numbers after the header. -/
def walkCom : Com :=
  .seq (.assign "jj" (.lit 0)) <| .seq (.assign "rem" (.lit 0)) <| .seq (.assign "e" (.lit 0)) <|
  .seq (.assign "L3" (sub (V "L") (.lit 3))) (forLoop "i" "L3" walkBody)

/-- The check: `ok` is `1` exactly when the numbers are those of an instance. -/
def chkCom : Com :=
  .seq (.assign "ok" (.lit 0)) <|
  .ite (.lt (.lit 2) (V "L"))
    (.ite (.lt (V "n") (add (V "L") (.lit 5)))
      (.ite (.lt (V "k") (add (V "n") (.lit 1)))
        (.seq walkCom
          (.ite (.eq (V "rem") (.lit 0))
            (.ite (.eq (V "jj") (V "m")) (.assign "ok" (.lit 1)) .skip) .skip))
        .skip) .skip) .skip

/-- The numbers of the construction. -/
def constCom : Com :=
  .seq (.assign "R" (add (mul (V "k") (sub (V "n") (.lit 1))) (.lit 2))) <|
  .seq (.assign "Q" (mul (sub (V "k") (.lit 1)) (add (V "n") (.lit 1)))) <|
  .seq (.assign "Lm" (V "e")) <|
  .seq (.assign "S" (mul (V "R") (V "Lm"))) <|
  .seq (.assign "mn" (mul (V "m") (V "n"))) <|
  .seq (.assign "Dc" (mul (V "R") (V "mn"))) <|
  .seq (.assign "N" (add (V "S") (mul (.lit 2) (V "Dc")))) <|
  .seq (.assign "T" (mul (mul (V "R") (V "m")) (sub (mul (.lit 2) (V "k")) (.lit 1)))) <|
  .assign "k1" (add (V "k") (.lit 1))

/-- The family, segment, set and element of job `t`. -/
def slotCom : Com :=
  .ite (.lt (V "t") (V "S"))
    (.seq (.assign "sg" (div (V "t") (V "Lm"))) <|
     .seq (.assign "ee" (sub (V "t") (mul (V "sg") (V "Lm")))) <|
     .seq (.assign "st" (.get "MJ" (V "ee"))) <|
     .seq (.assign "el" (.get "MI" (V "ee"))) (.assign "fam" (.lit 0)))
    (.seq (.assign "u" (sub (V "t") (V "S"))) <|
     .seq (.ite (.lt (V "u") (V "Dc")) (.seq (.assign "v" (V "u")) (.assign "fam" (.lit 1)))
            (.seq (.assign "v" (sub (V "u") (V "Dc"))) (.assign "fam" (.lit 2)))) <|
     .seq (.assign "sg" (div (V "v") (V "mn"))) <|
     .seq (.assign "st" (div (sub (V "v") (mul (V "sg") (V "mn"))) (V "n"))) <|
     .assign "el" (sub (V "v") (mul (div (V "v") (V "n")) (V "n"))))

/-- `g = r m + j + 1`. -/
def gCom : Com := .assign "g" (add (add (mul (V "sg") (V "m")) (V "st")) (.lit 1))

/-- The processing times of job `t`. -/
def pqCom : Com :=
  .ite (.eq (V "fam") (.lit 0))
    (.seq (.assign "P" (.lit 0)) (.assign "Qv" (mul (add (mul (.lit 2) (V "g")) (.lit 1)) (V "Q"))))
    (.seq (.assign "P" (mul (V "g") (add (V "n") (.lit 1))))
      (.ite (.eq (V "fam") (.lit 1)) (.assign "Qv" (mul (V "g") (V "Q")))
        (.assign "Qv" (mul (add (V "g") (.lit 1)) (V "Q")))))

/-- The tail of a record after the machine tuples. -/
def recTail : List ℕ := [0] ++ Lax434175.StandardReading.flat transList ++ [0]

/-- Write the record of job `t`. -/
def recCom : Com :=
  .seq (.write (add (mul (.lit 5) (V "k")) (.lit 27))) <| .seq (.write (.lit 2)) <|
  .seq (forLoop "c" "k1" (.seq (.write (V "P")) (incr "c"))) <|
  .seq (forLoop "c" "k1" (.seq (.write (V "Qv")) (incr "c"))) <|
  .seq (.write (.lit 0)) <| .seq (.write (V "k1")) <| .seq (writeList [2, 0, 0]) <|
  .seq (forLoop "c" "k" (.seq (writeList [2, 1]) (.seq (.write (add (V "c") (.lit 1))) (incr "c")))) <|
  writeList recTail

def recBody : Com := .seq slotCom (.seq gCom (.seq pqCom (.seq recCom (incr "t"))))

/-- The due date of job `t`. -/
def dCom : Com :=
  .ite (.eq (V "fam") (.lit 1))
    (.assign "d" (add (add (add (mul (mul (V "g") (V "g")) (V "Q")) (mul (V "g") (V "Q")))
      (V "el")) (.lit 1)))
    (.assign "d" (add (add (add (mul (mul (V "g") (V "g")) (V "Q"))
      (mul (add (mul (.lit 2) (V "g")) (.lit 1)) (V "Q"))) (V "el")) (.lit 1)))

def dueBody : Com :=
  .seq slotCom (.seq gCom (.seq dCom (.seq (writeList [0, 1]) (.seq (.write (V "d")) (incr "t")))))

/-- The threshold `N - target`. -/
def thrCom : Com :=
  .ite (.lt (V "N") (V "T")) (.seq (.write (.lit 1)) (.write (sub (V "T") (V "N"))))
    (.seq (.write (.lit 0)) (.write (sub (V "N") (V "T"))))

/-- Write the standard word. -/
def mainCom : Com :=
  .seq constCom <| .seq (writeList [0]) <| .seq (.write (V "N")) <| .seq (.write (V "k1")) <|
  .seq (forLoop "t" "N" recBody) <| .seq (writeList [0]) <|
  .seq (.ite (.eq (V "N") (.lit 0)) (writeList [0]) (writeList [1, 4, 1, 0, 0, 0])) <|
  .seq (forLoop "t" "N" dueBody) thrCom

/-- The program. -/
def emitCom : Com :=
  .seq Lax434175Proofs.Sanity.ReadAll.readAll <| .seq hdrCom <| .seq chkCom <|
    .ite (.eq (V "ok") (.lit 1)) mainCom .skip

end Lax434175Proofs.JitEmit
