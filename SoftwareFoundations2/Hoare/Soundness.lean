import SoftwareFoundations2.Hoare.Logic

open AExp
open BExp

namespace Hoare

set_option warn.sorry false in
lemma hoare_skip : ⊨ ⦃ P ⦄ ⟨{ skip }⟩ ⦃ P ⦄ := by
  sorry

set_option warn.sorry false in
lemma hoare_asgn : ⊨ ⦃ P[a // x] ⦄ ⟨{ ↑x = ↑a }⟩ ⦃ P ⦄ := by
  sorry

set_option warn.sorry false in
lemma hoare_seq
    (h₁ : ⊨ ⦃ P ⦄ c₁ ⦃ Q ⦄)
    (h₂ : ⊨ ⦃ Q ⦄ c₂ ⦃ R ⦄) :
  ⊨ ⦃ P ⦄ ⟨{ ↑c₁ ; ↑c₂}⟩ ⦃ R ⦄ := by
  sorry

set_option warn.sorry false in
lemma hoare_if {b : BExp}
      (h₁ : ⊨ ⦃ P ∧ b ⦄ c₁ ⦃ Q ⦄)
      (h₂ : ⊨ ⦃ P ∧ ¬b ⦄ c₂ ⦃ Q ⦄) :
  ⊨ ⦃ P ⦄ ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ⦃ Q ⦄ := by
  sorry

set_option warn.sorry false in
lemma hoare_while {b : BExp}
      (h : ⊨ ⦃ P ∧ b ⦄ c ⦃ P ⦄) :
  ⊨ ⦃ P ⦄ ⟨{ while ↑b do ↑c od }⟩ ⦃ P ∧ ¬b ⦄ := by
  sorry

set_option warn.sorry false in
lemma hoare_consequence
    (hPre : P ->> P')
    (hPost : Q' ->> Q)
    (hH : ⊨ ⦃ P' ⦄ c ⦃ Q' ⦄) :
  ⊨ ⦃ P ⦄ c ⦃ Q ⦄ := by
  sorry

def Soundness :
  ⊢ ⦃ P ⦄ c ⦃ Q ⦄ → ⊨ ⦃ P ⦄ c ⦃ Q ⦄ := by
  intro h
  induction h with
  | HSkip =>
      exact hoare_skip
  | HAsgn =>
      exact hoare_asgn
  | @HSeq P c₁ Q c₂ R _ _ ih₁ ih₂ =>
      apply hoare_seq
      repeat assumption
  | HIf _ _ ih₁ ih₂ =>
      apply hoare_if ih₁ ih₂
  | @HWhile P c b _ ih =>
      apply hoare_while ih
  | HConsequence h₁ h₂ _ ih =>
      apply hoare_consequence
      repeat assumption

end Hoare
