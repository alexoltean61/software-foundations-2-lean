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
  use AExp.APlus (AExp.AId "x") (AExp.ANum 1)
  intros h
  specialize h (State.init["x" ↦ 1]) (State.init["x" ↦ 2])
  simp only [Assertion.top, Assertion.eq, instEvalVar, ValThunk.ofVar, instEvalAExp,
    ValThunk.ofAExp, AExp.eval, Nat.left_eq_add, one_ne_zero, imp_false, not_true_eq_false] at h
  apply h.elim
  rw [State.init, default, instInhabitedState]
  simp only
  apply EAsgn
  · simp only [AExp.eval]
    unfold State.set
    simp
    rfl
  · unfold State.set
    simp only [beq_iff_eq]
    funext x
    by_cases x = "x"
    case pos h =>
      rw [h]
      simp
    case neg nh =>
      simp only [nh]
      simp

lemma Assertion.impl_self : P ->> P := by
  unfold Assertion.implies
  intros σ
  intros _
  assumption

def Hoare.HPreStrengthen : Proof P' c Q → (P ->> P') → Proof P c Q := by
  intros p'q pp'
  apply HConsequence
  · exact p'q
  · exact Assertion.impl_self
  · assumption

def Hoare.HPostWeaken : Proof P c Q' → (Q' ->> Q) → Proof P c Q := by
  intros pq' q'q
  apply HConsequence
  · exact pq'
  · assumption
  · exact Assertion.impl_self

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
  · apply Hoare.HPreStrengthen
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
    · apply HPreStrengthen
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
      · apply HWhile ⦃ z = (p + x) - m ⦄
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
    · apply HWhile ⦃ y + x = m ⦄
      · apply HSeq
        · apply HAsgn
        · apply HPreStrengthen
          · apply HAsgn
          · verify_assertion
    · verify_assertion
  · apply HPreStrengthen
    · apply HAsgn
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
      · apply HWhile ⦃ y * b + x = a ⦄
        · apply HSeq
          · apply HAsgn
          · apply HPreStrengthen
            · apply HAsgn
            · verify_assertion
      · verify_assertion
        · rw [mul_comm, eq_comm]
          apply natSumDiv a_2
        · rw [eq_comm]
          apply Nat.mod_eq_of_lt a_2
    · apply HAsgn
  · apply HPreStrengthen
    · apply HAsgn
    · verify_assertion

def fib : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n+2) => fib (n+1) + fib n

#eval fib 4

lemma fib_eqn (n : ℕ) (h : n > 0) :
  fib n + fib (n - 1) = fib (1 + n) := by
  induction n with
  | zero => contradiction
  | succ m ih =>
    simp only [add_tsub_cancel_right]
    rw [←add_assoc, add_comm (1 + m) 1, ←add_assoc, add_comm 2 m]
    rfl

def fibonacci {n : ℕ} :
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
  -- `fib_eqn`
  apply HSeq
  · apply HSeq
    · apply HSeq
      · apply HPostWeaken
        · apply HWhile (fun σ => (σ "x" > 0) ∧ (σ "y" = fib (σ "x" - 1)) ∧ (σ "z" = fib (σ "x")))
          · apply HSeq
            · apply HSeq
              · apply HSeq
                · apply HAsgn
                · apply HAsgn
              · apply HAsgn
            · apply HPreStrengthen
              · apply HAsgn
              · verify_assertion
                · apply fib_eqn
                  assumption
        · verify_assertion
      · apply HAsgn
    · apply HAsgn
  · apply HPreStrengthen
    · apply HAsgn
    · simp only [Assertion.implies, gt_iff_lt]
      intros σ
      unfold Assertion.subst
      unfold State.set
      simp only [String.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, AExp.eval, zero_lt_one,
        tsub_self, true_and]
      unfold fib
      simp
