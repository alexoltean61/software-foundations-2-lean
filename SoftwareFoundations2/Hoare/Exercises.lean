import SoftwareFoundations2.Hoare.Logic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Linarith

/- HELPERS -/
lemma mul4Inj {k n : ℕ} : ((4 * k) = (4 * n)) → k = n := by
  aesop

lemma consecutiveSquares {k n : ℕ} :
  (k * k ≤ n * n) → ((k+1) * (k+1) > n * n) → (k * k = n * n) := by
  intro h1 h2
  nlinarith [show k = n by nlinarith]

lemma natSumDiv {a b c : ℕ} (h : b < c) : (c * a + b) / c = a := by
  rw [ Nat.add_comm, Nat.add_mul_div_left _ _ ( pos_of_gt h ) ]
  norm_num [ h ]

lemma helperEq {i : ℕ} (h : 1 ≤ i) : ((i - 1) * (i - 1)) + (4 * i) = (i + 1) * i + (i + 1) := by
  zify [*] at *
  ring
--------------

open ComEval
open Hoare Proof

def hoare_asgn_wrong : ∃ a, ¬ ⊨ ⦃ ⊤ ⦄ ⟨{ x = ↑a }⟩ ⦃ x = a ⦄ := by
  exists aexp⟨{x + 1}⟩
  intro h
  unfold Valid at h
  simp only [Assertion.top, Assertion.eq, instEvalVar, ValThunk.ofVar, instEvalAExp,
    ValThunk.ofAExp, AExp.eval, Nat.left_eq_add, one_ne_zero, imp_false, not_true_eq_false] at h
  specialize h State.init (State.set State.init "x" (aexp⟨{x + 1}⟩.eval State.init))
  apply h
  apply EAsgn
  · rfl
  · rfl

lemma Assertion.impl_self : P ->> P := by
  unfold implies
  intros σ h
  exact h

def Hoare.HPreStrengthen : Proof P' c Q → (P ->> P') → Proof P c Q := by
  intros h hp
  apply HConsequence at h
  exact h Assertion.impl_self hp

def Hoare.HPostWeaken : Proof P c Q' → (Q' ->> Q) → Proof P c Q := by
  intros h hq
  apply HConsequence at h
  exact h hq Assertion.impl_self

def swap {n m : ℕ} :
  ⊢ ⦃ x = n ∧ y = m ⦄
      ⟨{
          x = x + y;
          y = x - y;
          x = x - y;
      }⟩
    ⦃ x = m ∧ y = n ⦄ := by
  apply HSeq
  · apply HSeq
    · apply HAsgn
    · apply HAsgn
  · apply HPreStrengthen
    · apply HAsgn
    · verify_assertion

def reduce_to_zero :
  ⊢ ⦃ ⊤ ⦄
      ⟨{
          while x != 0 do
            x = x - 1;
          od
      }⟩
    ⦃ x = 0 ⦄ := by
  apply HConsequence
  · apply HWhile ⦃ ⊤ ⦄
    apply HPreStrengthen
    · apply HAsgn
    · verify_assertion
  · verify_assertion
  · verify_assertion

def if_minus_plus_dec :
  ⊢ ⦃ ⊤ ⦄
      ⟨{
          if (x <= y) then
            z = y - x;
          else
            y = x + z;
          endif
      }⟩
    ⦃ y = x + z ⦄ := by
  apply HIf
  · apply HPreStrengthen
    · apply HAsgn
    · verify_assertion
  · apply HPreStrengthen
    · apply HAsgn
    · verify_assertion

def subtract_slowly {m p : ℕ} :
  ⊢ ⦃ ⊤ ⦄
      ⟨{
          x = ↑m;
          z = ↑p;
          while x != 0 do
            z = z - 1;
            x = x - 1;
          od
      }⟩
    ⦃ z = p - m ⦄ := by
  apply HSeq
  · apply HSeq
    · apply HPostWeaken
      · apply HWhile ⦃z - x = p - m⦄
        · apply HSeq
          · apply HAsgn
          · apply HPreStrengthen
            · apply HAsgn
            · verify_assertion
      · verify_assertion
    · apply HAsgn
  · apply HPreStrengthen
    · apply HAsgn
    · verify_assertion

def slow_assignment {m : ℕ} :
  ⊢ ⦃ "x" = m ⦄ -- ignore the apostrophes, fix is TODO for now, but meaning is as usual
      ⟨{
          y = 0;
          while x != 0 do
            x = x - 1;
            y = y + 1;
          od
      }⟩
    ⦃ "y" = m ⦄ := by
  apply HSeq
  · apply HPostWeaken
    · apply HWhile ⦃x + y = m⦄
      apply HSeq
      · apply HAsgn
      · apply HPreStrengthen
        · apply HAsgn
        · verify_assertion
    · verify_assertion
  · apply HConsequence
    · apply HAsgn
    · verify_assertion
    · verify_assertion


def div_mod_dec {a b : ℕ} :
  ⊢ ⦃ ⊤ ⦄
      ⟨{
        x = ↑a;
        y = 0;
        while (↑b <= x) do
          x = x - ↑b;
          y = y + 1;
        od
      }⟩
    ⦃ y = a / b ∧ x = a % b ⦄ := by
  -- OPTIONAL (PR will pass without it)
  -- You may need the following helper lemmas:
  -- `natSumDiv`, `Nat.mod_eq_of_lt`
  apply HSeq
  · apply HSeq
    · apply HPostWeaken
      · apply HWhile ⦃a = b * y + x⦄
        · apply HSeq
          · apply HAsgn
          · apply HPreStrengthen
            · apply HAsgn
            · verify_assertion
      · verify_assertion
        apply natSumDiv at a_2
        · symm
          exact a_2
        · symm
          exact Nat.mod_eq_of_lt a_2
    · apply HAsgn
  · apply HConsequence
    · apply HAsgn
    · verify_assertion
    · verify_assertion

#check Nat.mod_eq_of_lt

def fib : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n+2) => fib (n+1) + fib n

#eval fib 4

lemma fib_eqn (n : ℕ) (h : n > 0) :
  fib n + fib (n - 1) = fib (1 + n) := by
  induction n with
  | zero => simp_all only [lt_self_iff_false]
  | succ m hm =>
  simp only [add_tsub_cancel_right]
  nth_rw 3 [Nat.add_comm]
  rw [Nat.add_assoc]
  simp only [Nat.reduceAdd]
  rfl


def fibonacci {n f : ℕ} :
  ⊢ ⦃ ⊤ ⦄
      ⟨{
        x = 1;
        y = 1;
        z = 1;
        while x != 1 + ↑n do
          t = z;
          z = z + y;
          y = t;
          x = 1 + x;
        od
      }⟩
    ⦃ y = ↑(fib n) ⦄ := by
  -- OPTIONAL (PR will pass without it)
  -- You may need the following helper lemma:
  -- `fib_eqn`
  apply HSeq
  · apply HSeq
    · apply HSeq
      · apply HPostWeaken
        · apply HWhile (Assertion.and (fun σ => σ "x" > 0)
           (Assertion.and (fun σ => σ "z" = fib (σ "x")) (fun σ => σ "y" = fib (σ "x" - 1))))
          · apply HPreStrengthen
            · apply HSeq
              · apply HSeq
                · apply HSeq
                  · apply HAsgn
                  · apply HAsgn
                · apply HAsgn
              · apply HAsgn
            · verify_assertion
              apply fib_eqn
              exact a
        · verify_assertion
      · apply HAsgn
    · apply HAsgn
  · apply HConsequence
    · apply HAsgn
    · verify_assertion
      · sorry
      · sorry
    · verify_assertion
