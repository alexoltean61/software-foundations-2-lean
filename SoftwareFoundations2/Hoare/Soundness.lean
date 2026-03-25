import SoftwareFoundations2.Hoare.Logic

open AExp
open BExp

namespace Hoare

set_option warn.sorry false in
lemma hoare_skip : ⊨ ⦃ P ⦄ ⟨{ skip }⟩ ⦃ P ⦄ := by
  intros σ σ' h h1
  cases h with
  | ESkip => assumption

set_option warn.sorry false in
lemma hoare_asgn : ⊨ ⦃ P[a // x] ⦄ ⟨{ ↑x = ↑a }⟩ ⦃ P ⦄ := by
  intros σ σ' h h1
  cases h with
  | EAsgn h2 h3 =>
    rw [h2] at h3
    rw [Assertion.subst] at h1
    rw [← h3] at h1
    assumption

set_option warn.sorry false in
lemma hoare_seq
    (h₁ : ⊨ ⦃ P ⦄ c₁ ⦃ Q ⦄)
    (h₂ : ⊨ ⦃ Q ⦄ c₂ ⦃ R ⦄) :
  ⊨ ⦃ P ⦄ ⟨{ ↑c₁ ; ↑c₂}⟩ ⦃ R ⦄ := by
  intros σ σ' h h1
  cases h with
  | @ESeq _ _ σi _ ha hb hc =>
    specialize h₁ σ σi
    apply h₁ at hb
    apply hb at h1
    specialize h₂ σi σ'
    apply h₂ at hc
    apply hc at h1
    assumption

set_option warn.sorry false in
lemma hoare_if {b : BExp}
      (h₁ : ⊨ ⦃ P ∧ b ⦄ c₁ ⦃ Q ⦄)
      (h₂ : ⊨ ⦃ P ∧ ¬b ⦄ c₂ ⦃ Q ⦄) :
  ⊨ ⦃ P ⦄ ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ⦃ Q ⦄ := by
  intros σ σ' h h1
  cases h with
  | EIfTrue ha hb =>
    apply h₁ at hb
    apply hb
    rw [Assertion.and]
    rw [BExp.assert]
    exact And.intro h1 ha
  | EIfFalse ha hb =>
    apply h₂ at hb
    apply hb
    rw [Assertion.and, Assertion.neg]
    apply And.intro
    · assumption
    rw [BExp.assert, Bool.not_eq_true]
    assumption

set_option warn.sorry false in
lemma hoare_while {b : BExp}
      (h : ⊨ ⦃ P ∧ b ⦄ c ⦃ P ⦄) :
  ⊨ ⦃ P ⦄ ⟨{ while ↑b do ↑c od }⟩ ⦃ P ∧ ¬b ⦄ := by
  intros σ σ' h1 h2
  generalize eq : ⟨{ while ↑b do ↑c od }⟩ = loop at h1
  induction h1 with
  | EWhileFalse ha =>
    specialize h σ σ'
    cases eq
    rw [Assertion.and, Assertion.neg, BExp.assert, Bool.not_eq_true]
    exact And.intro h2 ha
  | @EWhileTrue σ1 c1 σ'' b1 σ2 ha hb hc _ ih =>
    cases eq
    rw [Assertion.and, Assertion.neg, BExp.assert, Bool.not_eq_true]
    specialize h σ1 σ''
    apply h at hb
    simp only [Assertion.and, Assertion.neg, assert, Bool.not_eq_true, forall_const, and_imp] at *
    apply hb at h2
    apply h2 at ha
    apply ih at ha
    assumption
  | _ => contradiction


set_option warn.sorry false in
lemma hoare_consequence
    (hPre : P ->> P')
    (hPost : Q' ->> Q)
    (hH : ⊨ ⦃ P' ⦄ c ⦃ Q' ⦄) :
  ⊨ ⦃ P ⦄ c ⦃ Q ⦄ := by
  intros σ σ' h h1
  specialize hPre σ
  rw [Assertion.impl] at hPre
  apply hPre at h1
  specialize hH σ σ'
  apply hH at h
  apply h at h1
  specialize hPost σ'
  rw [Assertion.impl] at hPost
  apply hPost
  assumption

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
