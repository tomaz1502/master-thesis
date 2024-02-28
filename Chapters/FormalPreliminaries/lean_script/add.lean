inductive Natural where
  | zero : Natural
  | succ : Natural -> Natural

open Natural

def add : Natural -> Natural -> Natural
  | zero,   m => m
  | succ n, m => succ (add n m)

/- theorem add_comm : ∀ (n m : Natural), add n m = add m n := fun n m => -/
/-   match n with -/
/-   | zero => rfl -/
/-   | succ n' => sorry -/

