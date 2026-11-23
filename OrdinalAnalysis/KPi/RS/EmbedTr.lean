module

public import OrdinalAnalysis.KPi.RS.HSim
public import OrdinalAnalysis.KPi.Language

/-!
# The RS calculus, part 30: the relativisation `φ ↦ φ^λ` of `ℒ_Ad`-formulas to `L_λ`

(The *uniform* reading: every quantifier of `ℒ_Ad` is restricted to `L_λ`; B92's reading, in which
`∀x(x ∉ t ∨ ψ)` is the restricted quantifier `∀x∈t ψ`, is obtained from it by the adaptor lemma of the
embedding stage.)

`trD lam vb vf φ : D0 M` is the `D0`-formula of `φ`, where the bound variables of `φ` are sent to the
variables `vb i` and the free variables to `vf x` of the context `Fin M` of the `D0`-formula.
`⊤ ↦ ∀x∈L_0 (x ∈ x)`, `⊥ ↦ ∃x∈L_0 (x ∉ x)`, `∀ ↦ ∀x∈L_λ`, `∃ ↦ ∃x∈L_λ`.

* `trD_neg`   : the translation commutes with `∼`;
* `trD_rew`   : the translation of a rewritten formula is the translation under the pulled-back variable
                assignments (hence `free`, `shift`, `subst` are instances);
* `trD_sim`   : two assignments that agree on the values give `Sim`-equivalent sentences.
-/

@[expose] public section

open Ordinal FFL FFL.FirstOrder

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

open OrdinalAnalysis.KPi (LAd AdRel)

/-! ### variable assignments -/

/-- the index in `Fin M` of a term (a variable, since `ℒ_Ad` has no function symbols). -/
def evT {k M : ℕ} (vb : Fin k → Fin M) (vf : ℕ → Fin M) : Semiterm LAd ℕ k → Fin M
  | .bvar i => vb i
  | .fvar x => vf x
  | .func f _ => f.elim

/-- the assignment under one more binder: the new bound variable `#0` is the last one. -/
def extV {k M : ℕ} (vb : Fin k → Fin M) : Fin (k + 1) → Fin (M + 1) :=
  Fin.cases (Fin.last M) (fun i => (vb i).castSucc)

def liftVf {M : ℕ} (vf : ℕ → Fin M) : ℕ → Fin (M + 1) := fun x => (vf x).castSucc

@[simp] theorem extV_zero {k M : ℕ} (vb : Fin k → Fin M) : extV vb 0 = Fin.last M := by
  simp [extV]

@[simp] theorem extV_succ {k M : ℕ} (vb : Fin k → Fin M) (i : Fin k) :
    extV vb i.succ = (vb i).castSucc := by
  simp [extV]

theorem evT_bShift {k M : ℕ} (vb : Fin k → Fin M) (vf : ℕ → Fin M) (t : Semiterm LAd ℕ k) :
    evT (extV vb) (liftVf vf) (Rew.bShift t) = (evT vb vf t).castSucc := by
  cases t with
  | bvar i => simp [evT]
  | fvar x => simp [evT, liftVf]
  | func f v => exact f.elim

/-! ### the translation -/

/-- the `D0`-formula of an `ℒ_Ad`-formula, relativised to `L_λ`. -/
def trD (lam : Ordinal.{1}) : ∀ {k M : ℕ}, (Fin k → Fin M) → (ℕ → Fin M) →
    Semiformula LAd ℕ k → D0 M
  | _, M, _, _, .verum => D0.ball (Bd.lev 0) (D0.mem (Fin.last M) (Fin.last M))
  | _, M, _, _, .falsum => D0.bex (Bd.lev 0) (D0.nmem (Fin.last M) (Fin.last M))
  | _, _, vb, vf, .rel AdRel.mem v => D0.mem (evT vb vf (v 0)) (evT vb vf (v 1))
  | _, _, vb, vf, .rel AdRel.ad v => D0.ad (evT vb vf (v 0))
  | _, _, vb, vf, .nrel AdRel.mem v => D0.nmem (evT vb vf (v 0)) (evT vb vf (v 1))
  | _, _, vb, vf, .nrel AdRel.ad v => D0.nad (evT vb vf (v 0))
  | _, _, vb, vf, .and φ ψ => D0.and (trD lam vb vf φ) (trD lam vb vf ψ)
  | _, _, vb, vf, .or φ ψ => D0.or (trD lam vb vf φ) (trD lam vb vf ψ)
  | _, _, vb, vf, .all φ => D0.ball (Bd.lev lam) (trD lam (extV vb) (liftVf vf) φ)
  | _, _, vb, vf, .exs φ => D0.bex (Bd.lev lam) (trD lam (extV vb) (liftVf vf) φ)

theorem trD_neg (lam : Ordinal.{1}) : ∀ {k M : ℕ} (vb : Fin k → Fin M) (vf : ℕ → Fin M)
    (φ : Semiformula LAd ℕ k), trD lam vb vf (∼φ) = (trD lam vb vf φ).neg := by
  intro k M vb vf φ
  induction φ using Semiformula.rec' generalizing M with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => cases r <;> rfl
  | hnrel r v => cases r <;> rfl
  | hand φ ψ ihφ ihψ => simp [trD, D0.neg, ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [trD, D0.neg, ihφ, ihψ]
  | hall φ ih => simp [trD, D0.neg, ih]
  | hexs φ ih => simp [trD, D0.neg, ih]


/-! ### rewriting -/

theorem evT_rew {k k' M : ℕ} (rw : Rew LAd ℕ k ℕ k') (vb : Fin k' → Fin M) (vf : ℕ → Fin M)
    (t : Semiterm LAd ℕ k) :
    evT vb vf (rw t) = evT (fun i => evT vb vf (rw #i)) (fun x => evT vb vf (rw &x)) t := by
  cases t with
  | bvar i => rfl
  | fvar x => rfl
  | func f v => exact f.elim

theorem trD_rew (lam : Ordinal.{1}) : ∀ {k k' M : ℕ} (rw : Rew LAd ℕ k ℕ k')
    (vb : Fin k' → Fin M) (vf : ℕ → Fin M) (φ : Semiformula LAd ℕ k),
    trD lam vb vf (rw ▹ φ) =
      trD lam (fun i => evT vb vf (rw #i)) (fun x => evT vb vf (rw &x)) φ := by
  intro k k' M rw vb vf φ
  induction φ using Semiformula.rec' generalizing k' M with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v =>
    cases r
    · simp only [Semiformula.rew_rel, trD]
      rw [evT_rew rw vb vf (v 0), evT_rew rw vb vf (v 1)]
    · simp only [Semiformula.rew_rel, trD]
      rw [evT_rew rw vb vf (v 0)]
  | hnrel r v =>
    cases r
    · simp only [Semiformula.rew_nrel, trD]
      rw [evT_rew rw vb vf (v 0), evT_rew rw vb vf (v 1)]
    · simp only [Semiformula.rew_nrel, trD]
      rw [evT_rew rw vb vf (v 0)]
  | hand φ ψ ihφ ihψ => simp [trD, ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [trD, ihφ, ihψ]
  | hall φ ih =>
    simp only [Rewriting.app_all, trD, ih]
    congr 2
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [evT, extV]
      · simp [evT_bShift, extV]
    · funext x
      simp [evT_bShift, liftVf]
  | hexs φ ih =>
    simp only [Rewriting.app_exs, trD, ih]
    congr 2
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [evT, extV]
      · simp [evT_bShift, extV]
    · funext x
      simp [evT_bShift, liftVf]


/-! ### assignments that agree on the values -/

theorem evT_val {α : Type*} {k M M' : ℕ} {vb : Fin k → Fin M} {vf : ℕ → Fin M}
    {vb' : Fin k → Fin M'} {vf' : ℕ → Fin M'} (e : Fin M → α) (e' : Fin M' → α)
    (hb : ∀ i, e (vb i) = e' (vb' i)) (t : Semiterm LAd ℕ k)
    (hf : ∀ x ∈ t.freeVariables, e (vf x) = e' (vf' x)) :
    e (evT vb vf t) = e' (evT vb' vf' t) := by
  cases t with
  | bvar i => exact hb i
  | fvar x => exact hf x (by simp [Semiterm.freeVariables])
  | func f v => exact f.elim

theorem fv_rel_term {k k' : ℕ} {r : LAd.Rel k'} {v : Fin k' → Semiterm LAd ℕ k} (i : Fin k') :
    ∀ x ∈ (v i).freeVariables, x ∈ (Semiformula.rel r v).freeVariables := by
  intro x hx
  simp only [Semiformula.freeVariables_rel, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨i, hx⟩

theorem fv_nrel_term {k k' : ℕ} {r : LAd.Rel k'} {v : Fin k' → Semiterm LAd ℕ k} (i : Fin k') :
    ∀ x ∈ (v i).freeVariables, x ∈ (Semiformula.nrel r v).freeVariables := by
  intro x hx
  simp only [Semiformula.freeVariables_nrel, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨i, hx⟩

theorem ext_extV {α : Type*} {k M M' : ℕ} {vb : Fin k → Fin M} {vb' : Fin k → Fin M'}
    {e : Fin M → α} {e' : Fin M' → α} (hb : ∀ i, e (vb i) = e' (vb' i)) (a : α) :
    ∀ i, ext e a (extV vb i) = ext e' a (extV vb' i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [hb j]

theorem kD_tr_eq (lam : Ordinal.{1}) : ∀ {k M M' : ℕ} (vb : Fin k → Fin M) (vf : ℕ → Fin M)
    (vb' : Fin k → Fin M') (vf' : ℕ → Fin M') (e : Fin M → Set Ordinal.{1})
    (e' : Fin M' → Set Ordinal.{1}) (φ : Semiformula LAd ℕ k),
    (∀ i, e (vb i) = e' (vb' i)) → (∀ x ∈ φ.freeVariables, e (vf x) = e' (vf' x)) →
    kD (trD lam vb vf φ) e = kD (trD lam vb' vf' φ) e' := by
  intro k M M' vb vf vb' vf' e e' φ
  induction φ using Semiformula.rec' generalizing M M' e e' with
  | hverum => intro _ _; simp [trD, kD, kBd]
  | hfalsum => intro _ _; simp [trD, kD, kBd]
  | hrel r v =>
    intro hb hf
    cases r
    · simp only [trD, kD]
      rw [evT_val e e' hb (v 0) (fun x hx => hf x (fv_rel_term 0 x hx)),
        evT_val e e' hb (v 1) (fun x hx => hf x (fv_rel_term 1 x hx))]
    · simp only [trD, kD]
      rw [evT_val e e' hb (v 0) (fun x hx => hf x (fv_rel_term 0 x hx))]
  | hnrel r v =>
    intro hb hf
    cases r
    · simp only [trD, kD]
      rw [evT_val e e' hb (v 0) (fun x hx => hf x (fv_nrel_term 0 x hx)),
        evT_val e e' hb (v 1) (fun x hx => hf x (fv_nrel_term 1 x hx))]
    · simp only [trD, kD]
      rw [evT_val e e' hb (v 0) (fun x hx => hf x (fv_nrel_term 0 x hx))]
  | hand φ ψ ihφ ihψ =>
    intro hb hf
    simp only [trD, kD]
    rw [ihφ vb vf vb' vf' e e' hb (fun x hx => hf x (by simp [hx])),
      ihψ vb vf vb' vf' e e' hb (fun x hx => hf x (by simp [hx]))]
  | hor φ ψ ihφ ihψ =>
    intro hb hf
    simp only [trD, kD]
    rw [ihφ vb vf vb' vf' e e' hb (fun x hx => hf x (by simp [hx])),
      ihψ vb vf vb' vf' e e' hb (fun x hx => hf x (by simp [hx]))]
  | hall φ ih =>
    intro hb hf
    simp only [trD, kD, kBd]
    rw [ih (extV vb) (liftVf vf) (extV vb') (liftVf vf') (ext e ∅) (ext e' ∅) ?_ ?_]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [hb j]
    · intro x hx
      simp [liftVf, hf x hx]
  | hexs φ ih =>
    intro hb hf
    simp only [trD, kD, kBd]
    rw [ih (extV vb) (liftVf vf) (extV vb') (liftVf vf') (ext e ∅) (ext e' ∅) ?_ ?_]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [hb j]
    · intro x hx
      simp [liftVf, hf x hx]


/-! ### `Sim`-invariance of the translation -/

theorem trD_sim {R : Set Ordinal.{1}} (lam : Ordinal.{1}) :
    ∀ {k M M' : ℕ} (vb : Fin k → Fin M) (vf : ℕ → Fin M) (vb' : Fin k → Fin M')
      (vf' : ℕ → Fin M') (ρ : Fin M → T) (ρ' : Fin M' → T) (φ : Semiformula LAd ℕ k),
    (∀ i, ρ (vb i) = ρ' (vb' i)) → (∀ x ∈ φ.freeVariables, ρ (vf x) = ρ' (vf' x)) →
    Sim R (RSS.base (trD lam vb vf φ) ρ) (RSS.base (trD lam vb' vf' φ) ρ') := by
  intro k M M' vb vf vb' vf' ρ ρ' φ
  induction φ using Semiformula.rec' generalizing M M' ρ ρ' with
  | hverum =>
    intro hb hf
    refine sim_ball_gen (Bd.lev 0) (Bd.lev 0) _ _ ρ ρ' rfl (fun t => ?_) ?_
    · exact sim_mem_atom _ _ _ _ _ _ (by simp) (by simp)
    · exact kD_tr_eq lam vb vf vb' vf' (fun i => (ρ i).k) (fun i => (ρ' i).k) ⊤
        (fun i => by simp [hb i]) (fun x hx => by simp at hx)
  | hfalsum =>
    intro hb hf
    refine sim_bex_gen (Bd.lev 0) (Bd.lev 0) _ _ ρ ρ' rfl (fun t => ?_) ?_
    · exact sim_nmem_atom _ _ _ _ _ _ (by simp) (by simp)
    · exact kD_tr_eq lam vb vf vb' vf' (fun i => (ρ i).k) (fun i => (ρ' i).k) ⊥
        (fun i => by simp [hb i]) (fun x hx => by simp at hx)
  | hrel r v =>
    intro hb hf
    cases r
    · exact sim_mem_atom _ _ _ _ ρ ρ' (evT_val ρ ρ' hb (v 0) (fun x hx => hf x (fv_rel_term 0 x hx)))
        (evT_val ρ ρ' hb (v 1) (fun x hx => hf x (fv_rel_term 1 x hx)))
    · exact sim_ad_atom _ _ ρ ρ' (evT_val ρ ρ' hb (v 0) (fun x hx => hf x (fv_rel_term 0 x hx)))
  | hnrel r v =>
    intro hb hf
    cases r
    · exact sim_nmem_atom _ _ _ _ ρ ρ' (evT_val ρ ρ' hb (v 0) (fun x hx => hf x (fv_nrel_term 0 x hx)))
        (evT_val ρ ρ' hb (v 1) (fun x hx => hf x (fv_nrel_term 1 x hx)))
    · exact sim_nad_atom _ _ ρ ρ' (evT_val ρ ρ' hb (v 0) (fun x hx => hf x (fv_nrel_term 0 x hx)))
  | hand φ ψ ihφ ihψ =>
    intro hb hf
    exact sim_band_gen _ _ _ _ ρ ρ' (ihφ vb vf vb' vf' ρ ρ' hb (fun x hx => hf x (by simp [hx])))
      (ihψ vb vf vb' vf' ρ ρ' hb (fun x hx => hf x (by simp [hx])))
  | hor φ ψ ihφ ihψ =>
    intro hb hf
    exact sim_bor_gen _ _ _ _ ρ ρ' (ihφ vb vf vb' vf' ρ ρ' hb (fun x hx => hf x (by simp [hx])))
      (ihψ vb vf vb' vf' ρ ρ' hb (fun x hx => hf x (by simp [hx])))
  | hall φ ih =>
    intro hb hf
    refine sim_ball_gen (Bd.lev lam) (Bd.lev lam) _ _ ρ ρ' rfl (fun t => ?_) ?_
    · refine ih (extV vb) (liftVf vf) (extV vb') (liftVf vf') (ext ρ t) (ext ρ' t)
        (ext_extV hb t) (fun x hx => ?_)
      simp [liftVf, hf x hx]
    · exact kD_tr_eq lam vb vf vb' vf' (fun i => (ρ i).k) (fun i => (ρ' i).k) (∀¹ φ)
        (fun i => by simp [hb i]) (fun x hx => by simp [hf x hx])
  | hexs φ ih =>
    intro hb hf
    refine sim_bex_gen (Bd.lev lam) (Bd.lev lam) _ _ ρ ρ' rfl (fun t => ?_) ?_
    · refine ih (extV vb) (liftVf vf) (extV vb') (liftVf vf') (ext ρ t) (ext ρ' t)
        (ext_extV hb t) (fun x hx => ?_)
      simp [liftVf, hf x hx]
    · exact kD_tr_eq lam vb vf vb' vf' (fun i => (ρ i).k) (fun i => (ρ' i).k) (∃¹ φ)
        (fun i => by simp [hb i]) (fun x hx => by simp [hf x hx])

end OrdinalAnalysis.KPi.RS
