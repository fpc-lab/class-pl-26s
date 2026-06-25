/-
Simply-Type λ-Calculus <--> Propositional Logic
-/
namespace PropLogic

variable (A B C : Type)
variable (P Q R : Prop)

--
-- function type <--> implication
--
def fun_prog1 : A -> A :=
  -- identity function
  fun x => x
def fun_prog2 : (A -> B) -> (B -> C) -> (A -> C) :=
  -- composition function
  fun f => fun g => (fun x => g (f x))

theorem fun_proof1 : P → P :=
  fun x => x
theorem fun_proof2 : (P → Q) → (Q → R) → (P → R) :=
  fun f => fun g => (fun x => g (f x))

--
-- product type <--> conjunction
--
def prod_prog1 : ((A × B) -> C) -> (A -> B -> C) :=
  -- currying function
  fun f => (fun x => fun y => f (x, y))
def prod_prog2 : (A -> B -> C) -> ((A × B) -> C) :=
  -- uncurrying function
  fun f => (fun x => f (Prod.fst x) (Prod.snd x))

theorem prod_proof1 : ((P ∧ Q) → R) → (P → Q → R) :=
  fun f => (fun x => fun y => f ⟨x, y⟩)
theorem prod_proof2 : (P → Q → R) → ((P ∧ Q) → R) :=
  fun f => (fun x => f (And.left x) (And.right x))
theorem prod_proof2' : (P → Q → R) → ((P ∧ Q) → R) := by
  -- alternative proof using "tatics"
  intro hpqr
  intro hpq
  apply hpqr
  . exact hpq.left
  . exact hpq.right

--
-- sum type <--> disjunction
--
def sum_prog1 : (A ⊕ B) -> (B ⊕ A) :=
  fun x => match x with
  | Sum.inl y1 => Sum.inr y1
  | Sum.inr y2 => Sum.inl y2
def sum_prog2 : (A -> C) -> (B -> C) -> ((A ⊕ B) -> C) :=
  fun f => fun g =>
    (fun x => match x with
    | Sum.inl y1 => f y1
    | Sum.inr y2 => g y2)

theorem sum_proof1 : (P ∨ Q) → (Q ∨ P) :=
  fun x => match x with
  | Or.inl y1 => Or.inr y1
  | Or.inr y2 => Or.inl y2
theorem sum_proof2 : (P → R) → (Q → R) → ((P ∨ Q) → R) :=
  fun f => fun g =>
    (fun x => match x with
    | Or.inl y1 => f y1
    | Or.inr y2 => g y2)

end PropLogic


/-
Dependently-Typed λ-Calculus <--> First-Order Logic
-/
namespace FOLogic

--
-- Syntactic category "Nat":
--   Nat n ::= Z | S n
--
-- Judgment "Eq n m":
--                     Eq n m
--   ====== EqZ    ============== EqS
--   Eq Z Z        Eq (S n) (S m)
--
inductive Nat where
  | Z           : Nat  -- Z
  | S (n : Nat) : Nat  -- S n
open Nat

inductive Eq : Nat → Nat → Prop where
  | EqZ                    : Eq Z Z          -- EqZ
  | EqS {n m} (h : Eq n m) : Eq (S n) (S m)  -- EqS
open Eq

def _n0 := (Z       : Nat)
def _n1 := (S Z     : Nat)
def _e0 := (EqZ     : Eq Z Z)
def _e1 := (EqS EqZ : Eq (S Z) (S Z))

--
-- Function "double":
--   double n = (2 * n) in Nat.
--
-- Theorem "half_exist":
--   For every n, there exists m such that n = double(m) or n = double(m)+1.
--
def double : Nat → Nat :=
  fun n => match n with
  | Z    => Z                   -- double(0) = 0.
  | S n' => S (S (double n'))  -- double(n'+1) = double(n')+2.

theorem half_exist : ∀ n : Nat, ∃ m : Nat, Eq n (double m) ∨ Eq n (S (double m)) :=
  fun n => match n with
  | Z    =>
      -- Case n = 0: Then, n = double(0).
      ⟨Z, Or.inl EqZ⟩
  | S n' =>
      -- Case n = n'+1:
      -- * If n' = double(m'),   then n = double(m') + 1. [left  case in ∨]
      -- * If n' = double(m')+1, then n = double(m'+1).   [right case in ∨]
      match half_exist n' with
      | ⟨m', Or.inl h⟩ => ⟨m',   Or.inr (EqS h)⟩
      | ⟨m', Or.inr h⟩ => ⟨S m', Or.inl (EqS h)⟩

--
-- Function "half":
--   half n = (m, b), where n = double(m) if b = true, and n = double(m)+1 if b = false.
--
def half : Nat → Nat × Bool :=
  fun n => match n with
  | Z => (Z, true)
  | S n =>
      match half n with
      | (m, true ) => (m,   false)
      | (m, false) => (S m, true )

end FOLogic
