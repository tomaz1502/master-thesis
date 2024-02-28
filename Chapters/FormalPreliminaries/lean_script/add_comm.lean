inductive Natural where
  | zero : Natural
  | succ : Natural -> Natural

open Natural

def add (n m : Natural) : Natural :=
  match n with
  | zero => m
  | succ n => succ (add n m)

notation x " + " y => add x y

def add_zero' : forall (n : Natural), (n + zero) = n := fun n =>
  match n with
  | zero => rfl
  | succ n' => congrArg succ (add_zero' n')

#print add_zero'

theorem add_succ' : ∀ (n m : Natural), (n + succ m) = succ (n + m) := fun n m =>
  match n with
  | zero => rfl
  | succ n' => congrArg succ (add_succ' n' m)

theorem add_comm' : ∀ (n m : Natural), (n + m) = (m + n) := fun n m =>
  match n with
  | zero => Eq.symm (add_zero' m)
  | succ n' => 
    Eq.trans (congrArg succ (add_comm' n' m)) (Eq.symm (add_succ' m n'))

theorem add_zero : ∀ (n : Natural), (n + zero) = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n' IH => rw [add, IH]

theorem add_succ : ∀ (n m : Natural), (n + succ m) = succ (n + m) := by
  intros n m
  induction n with
  | zero => rfl
  | succ n' IH => rw [add, add, IH]

theorem add_comm : ∀ (n m : Natural), (n + m) = (m + n) := by
  intros n m
  induction n with
  | zero => rw [add, add_zero]
  | succ n' IH => rw [add, add_succ, IH]

#print add_comm'
#print add_comm
