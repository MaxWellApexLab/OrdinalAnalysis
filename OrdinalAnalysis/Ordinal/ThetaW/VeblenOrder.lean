/-
  Order preservation for the multi-level Veblen function `φ_k` (`ThetaW/Veblen.lean`), under the
  domain regime `ρ, β ≺ Ω_{k+1}` (`dom_phi_of_lt`).

  Source: A. Freund, arXiv:2204.09321, Lemma 7.7 / Definition 7.6, one level up (see
  `Veblen.lean`'s module docstring for the precise correspondence `φ_k(ρ,β) := ϑ_k(Ω_{k+1}·ρ+β)`
  and why its order properties were left unattempted there).  the design notes item 1c
  identifies the three facts the predicative cut elimination step actually consumes (Buchholz
  1992's `φ.2`–`φ.4`, restricted to the domain `ρ, β ≺ Ω_{k+1}`):
  * `φ.3` (monotonicity in `β`) — `phi_lt_phi_right`;
  * the mixed comparison with `ρ < ρ'` — `phi_lt_phi_of_lt_left`;
  * `φ.2` (additive closure below `φ`) — `lt_phi_of_lt`.

  The tool throughout is the same-level clause `theta_lt_theta_iff` (`ThetaW/Order.lean`) with
  the coefficient set `E k` — *not* `G k` (`ThetaW/Dom.lean`'s domain-side coefficient set, which
  vanishes on every term `≺ Ω_{k+1}` and is therefore useless for the order, since `E_k` of such
  a term need not vanish).  The first new content this file needs, absent from `ThetaW/Arith`,
  is how `E_k` interacts with `Ω_{k+1} + ·` and with the exponent-list sum `addL`:
  * `E_omegaAdd_eq_of_lt`: `E_k(Ω_{k+1} + e) = E_k(e)` whenever `e ≺ Ω_{k+1}` (the same
    "leading term dominates" fact that already drives `omegaAdd`'s definition, read off through
    `E_k` instead of through the raw order);
  * `E_phiArg_eq_of_lt`: consequently `E_k(Ω_{k+1}·ρ + β) = E_k(ρ) ++ E_k(β)` whenever
    `ρ, β ≺ Ω_{k+1}` — the argument of `φ_k` splits cleanly into a `ρ`-part and a `β`-part at the
    level of coefficients, even though as a *term* it sits above `Ω_{k+1}`.

  Everything downstream is bookkeeping with `theta_lt_theta_iff`'s two branches and the already
  proved one-level lemmas `theta_lt_theta_of_lt_level`, `le_of_mem_E`, `exists_eq_theta_of_mem_E`,
  `exists_mem_E_of_theta_le`, `theta_lt_theta_of_le_mem_E` of `ThetaW/Order.lean` — none of which
  needed to be re-proved, only re-applied one level up with `E_phiArg_eq_of_lt` supplying the
  bridge that the one-level system does not need (there, `ϑ`'s argument has no `Ω · ρ` shift).
-/
import OrdinalAnalysis.Ordinal.ThetaW.Veblen

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWTerm

/-! ### `E_k` and `Ω_{k+1} + ·` -/

/-- `ofList` of a list built by prepending `Ω_{k+1}` to `E_k`-summed lists: general form used
below, avoiding re-deriving the `addL` computation twice. -/
theorem addL_Omega_cons_toList_of_lt {k : ℕ} {e : ThetaWTerm} (h : e < Omega k) :
    addL [Omega k] (toList e) = Omega k :: toList e := by
  rcases shape e with hp | rfl | ⟨c, cs, rfl⟩
  · have hfilter : ([Omega k] : List ThetaWTerm).filter (fun x => geb x e) = [Omega k] :=
      List.filter_eq_self.mpr fun x hx => by
        rw [List.mem_singleton] at hx; subst hx; simp [geb, le_of_lt' h]
    rw [toList_of_isPrin hp, addL_cons, hfilter]; rfl
  · simp
  · have hc : c < Omega k := (cons_lt_Omega_iff k c cs).mp h
    have hfilter : ([Omega k] : List ThetaWTerm).filter (fun x => geb x c) = [Omega k] :=
      List.filter_eq_self.mpr fun x hx => by
        rw [List.mem_singleton] at hx; subst hx; simp [geb, le_of_lt' hc]
    rw [toList_sum, addL_cons, hfilter]; rfl

/-- `Ω_{k+1} + e` always dominates `Ω_{k+1}` itself: it either *is* `Ω_{k+1}` (when `e = 0`) or
strictly exceeds it (when `e ≠ 0`, via `Omega_lt_cons_iff`). -/
theorem Omega_le_omegaAdd_of_lt {k : ℕ} {e : ThetaWTerm} (h : e < Omega k) :
    Omega k ≤ omegaAdd k e := by
  unfold omegaAdd
  rw [addL_Omega_cons_toList_of_lt h]
  rcases shape e with hp | rfl | ⟨c, cs, rfl⟩
  · rw [toList_of_isPrin hp, show ofList (Omega k :: [e]) = sum (Omega k :: [e]) from rfl]
    exact le_of_lt' ((Omega_lt_cons_iff k (Omega k) [e]).mpr (le_refl' _))
  · simp [ofList_singleton_prin (isPrin_Omega k)]
  · rw [toList_sum, show ofList (Omega k :: c :: cs) = sum (Omega k :: c :: cs) from rfl]
    exact le_of_lt' ((Omega_lt_cons_iff k (Omega k) (c :: cs)).mpr (le_refl' _))

/-- **The coefficient bridge.** `E_k(Ω_{k+1} + e) = E_k(e)` whenever `e ≺ Ω_{k+1}`: `Ω_{k+1}`
itself contributes nothing to `E_k` (`E_Omega`), and the rest of the list is exactly `toList e`,
whose `E_k`-sum is `E_k(e)` by the sum-clause of `E` (definitionally, `sum (toList e)` and `e`
agree on `E_k` even when `ofList (toList e)` collapses `e`'s own singleton back to a principal
term). -/
theorem E_omegaAdd_eq_of_lt {k : ℕ} {e : ThetaWTerm} (h : e < Omega k) :
    E k (omegaAdd k e) = E k e := by
  unfold omegaAdd
  rw [addL_Omega_cons_toList_of_lt h]
  rcases shape e with hp | rfl | ⟨c, cs, rfl⟩
  · rw [toList_of_isPrin hp, show ofList (Omega k :: [e]) = sum (Omega k :: [e]) from rfl,
      E_cons, E_Omega, List.nil_append, E_cons, E_nil, List.append_nil]
  · simp [ofList_singleton_prin (isPrin_Omega k)]
  · rw [toList_sum, show ofList (Omega k :: c :: cs) = sum (Omega k :: c :: cs) from rfl,
      E_cons, E_Omega, List.nil_append]

/-- `E_k(ofList L) = EList k L`, for any exponent list `L` (whether or not `ofList` collapses a
singleton to a principal term — `EList` erases the difference). -/
theorem E_ofList (k : ℕ) (L : List ThetaWTerm) : E k (ofList L) = EList k L := by
  match L with
  | [] => rfl
  | [x] =>
    by_cases h : IsPrin x
    · rw [ofList_singleton_prin h]
      show E k x = EList k [x]
      simp [EList]
    · rw [ofList_singleton_not_prin h]
      show E k (sum [x]) = EList k [x]
      simp [E, EList]
  | _ :: _ :: _ => rfl

/-- `E_k(t) = EList_k(toList t)`, for normal `t` — the two-sided form of `E_ofList` that lets
callers state the result in terms of `toList`/`entries` directly, without going through
`ofList`. -/
theorem E_eq_EList_toList {t : ThetaWTerm} (ht : NF t) (k : ℕ) :
    E k t = EList k (toList t) := by
  conv_lhs => rw [← ofList_toList ht]
  exact E_ofList k (toList t)

/-- `EList` distributes over list append. -/
theorem EList_append (k : ℕ) : ∀ (xs ys : List ThetaWTerm),
    EList k (xs ++ ys) = EList k xs ++ EList k ys
  | [], _ys => rfl
  | x :: xs, ys => by
      show E k x ++ EList k (xs ++ ys) = (E k x ++ EList k xs) ++ EList k ys
      rw [EList_append k xs ys, List.append_assoc]

/-- `EList` is unchanged by mapping `Ω_{k+1} + ·` over a list all of whose entries are `≺
Ω_{k+1}` (entrywise `E_omegaAdd_eq_of_lt`). -/
theorem EList_map_omegaAdd_eq_of_forall_lt {k : ℕ} {L : List ThetaWTerm}
    (hL : ∀ e ∈ L, e < Omega k) : EList k (L.map (omegaAdd k)) = EList k L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    show E k (omegaAdd k x) ++ EList k (xs.map (omegaAdd k)) = E k x ++ EList k xs
    rw [E_omegaAdd_eq_of_lt (hL x List.mem_cons_self),
      ih (fun e he => hL e (List.mem_cons_of_mem x he))]

/-- Dominance forces literal concatenation: if every entry of `ys` is `≼` every entry of `xs`,
`addL xs ys` does not merge anything away from `xs`. -/
theorem addL_append_of_forall_le {xs ys : List ThetaWTerm}
    (h : ∀ x ∈ xs, ∀ y ∈ ys, y ≤ x) : addL xs ys = xs ++ ys := by
  cases ys with
  | nil => simp
  | cons y ys' =>
    rw [addL_cons]
    congr 1
    refine List.filter_eq_self.mpr fun x hx => ?_
    simp only [geb, decide_eq_true_eq]
    exact h x hx y List.mem_cons_self

end ThetaWTerm

namespace ThetaWNoteD

open ThetaWTerm

/-! ### The coefficient set of `φ_k`'s argument -/

/-- **The structural bridge.** `E_k(Ω_{k+1}·ρ + β) = E_k(ρ) ++ E_k(β)` whenever `ρ, β ≺
Ω_{k+1}`: every entry of `Ω_{k+1}·ρ` is `≽ Ω_{k+1}` (`Omega_le_omegaAdd_of_lt`) and every entry
of `β` is `≺ Ω_{k+1}` (`lt_prin_iff`), so `addL` does not merge across the two parts
(`addL_append_of_forall_le`); `E_k` of the concatenation is then the concatenation of the
`E_k`'s (`EList_append`), and `E_k` of `Ω_{k+1}·ρ`'s entries collapses to `E_k` of `ρ`'s own
entries by `EList_map_omegaAdd_eq_of_forall_lt`. -/
theorem E_phiArg_eq_of_lt {k : ℕ} {rho beta : ThetaWNoteD} (hrho : rho < Omega k)
    (hbeta : beta < Omega k) :
    ThetaWTerm.E k (phiArg k rho beta).1 = ThetaWTerm.E k rho.1 ++ ThetaWTerm.E k beta.1 := by
  have hrho' : ∀ e ∈ rho.entries, e < (ThetaWTerm.Omega k) := (lt_prin_iff (isPrin_Omega k)).mp hrho
  have hbeta' : ∀ e ∈ beta.entries, e < (ThetaWTerm.Omega k) :=
    (lt_prin_iff (isPrin_Omega k)).mp hbeta
  have hentries : (phiArg k rho beta).entries =
      (omegaMulOmega k rho).entries ++ beta.entries := by
    show (omegaMulOmega k rho + beta).entries = _
    rw [entries_add]
    refine addL_append_of_forall_le fun x hx y hy => ?_
    have hx' : ThetaWTerm.Omega k ≤ x := by
      rw [entries_omegaMulOmega] at hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact Omega_le_omegaAdd_of_lt (hrho' e he)
    exact le_trans' (le_of_lt' (hbeta' y hy)) hx'
  have step1 : ThetaWTerm.E k (phiArg k rho beta).1 =
      ThetaWTerm.EList k (phiArg k rho beta).entries := E_eq_EList_toList (phiArg k rho beta).2.1 k
  have step2 : ThetaWTerm.EList k (omegaMulOmega k rho).entries = ThetaWTerm.E k rho.1 := by
    rw [entries_omegaMulOmega, EList_map_omegaAdd_eq_of_forall_lt hrho']
    exact (E_eq_EList_toList rho.2.1 k).symm
  have step3 : ThetaWTerm.EList k beta.entries = ThetaWTerm.E k beta.1 :=
    (E_eq_EList_toList beta.2.1 k).symm
  rw [step1, hentries, EList_append, step2, step3]

/-! ### `φ_k` order preservation -/

/-- **`φ.3`: `φ_k` is strictly monotone in `β`** (Freund, Lemma 7.7 / Def 7.6, one level up;
the design notes item 1c). The only fact the predicative cut-elimination step needs
from this file at every use site of `phi_lt_phi_right`. -/
theorem phi_lt_phi_right {k : ℕ} {rho beta beta' : ThetaWNoteD} (hrho : rho < Omega k)
    (hbeta : beta < Omega k) (hbeta' : beta' < Omega k) (h : beta < beta') :
    phi k rho beta < phi k rho beta' := by
  unfold phi
  have harg : phiArg k rho beta < phiArg k rho beta' := phiArg_lt_phiArg_of_lt rho h
  refine (theta_lt_theta_iff k _ _).mpr (Or.inl ⟨harg, fun g hg => ?_⟩)
  rw [E_phiArg_eq_of_lt hrho hbeta, List.mem_append] at hg
  rcases hg with hg | hg
  · -- `g` comes from `E_k(ρ)`: bounded by `ρ` itself, which is `≺ Ω_{k+1}`.
    obtain ⟨j, δ, hjk, rfl⟩ := exists_eq_theta_of_mem_E hg
    rcases hjk.lt_or_eq with hj | hj
    · exact theta_lt_theta_of_lt_level δ (phiArg k rho beta').1 hj
    · rw [hj] at hg ⊢
      refine theta_lt_theta_of_le_mem_E ?_ (le_refl' (ThetaWTerm.theta k δ))
      rw [E_phiArg_eq_of_lt hrho hbeta']
      exact List.mem_append_left _ hg
  · -- `g` comes from `E_k(β)`: bounded via `β ≺ β'` and `exists_mem_E_of_theta_le`.
    obtain ⟨j, δ, hjk, rfl⟩ := exists_eq_theta_of_mem_E hg
    rcases hjk.lt_or_eq with hj | hj
    · exact theta_lt_theta_of_lt_level δ (phiArg k rho beta').1 hj
    · rw [hj] at hg ⊢
      have hle : theta k δ ≤ beta.1 := le_of_mem_E beta.2.1 hg
      have hlt : theta k δ ≤ beta'.1 := le_of_lt' (lt_of_le_of_lt' hle h)
      obtain ⟨g', hg', hg'le⟩ := exists_mem_E_of_theta_le δ hbeta' hlt
      refine theta_lt_theta_of_le_mem_E ?_ hg'le
      rw [E_phiArg_eq_of_lt hrho hbeta']
      exact List.mem_append_right _ hg'

/-- **`φ.2`: `φ_k(ρ,β)` is additively closed** (Freund, Lemma 7.7 / Def 7.6, one level up;
the design notes item 1c): any two notations below `φ_k(ρ,β)` have their sum below it
too. This is exactly `add_lt_prin`, since `φ_k(ρ,β) = ϑ_k(⋯)` is always a principal term
(`isPrin_theta`) once it is known to be in the domain (`dom_phi_of_lt`), which the same
hypotheses `ρ, β ≺ Ω_{k+1}` supply. No new order argument over `E_k` is needed for this one. -/
theorem lt_phi_of_lt {k : ℕ} {rho beta : ThetaWNoteD} (hrho : rho < Omega k)
    (hbeta : beta < Omega k) {xi eta : ThetaWNoteD} (hxi : xi.1 < phi k rho beta)
    (heta : eta.1 < phi k rho beta) : (xi + eta).1 < phi k rho beta :=
  add_lt_prin (p := ⟨phi k rho beta, nf_phi k rho beta, dom_phi_of_lt hrho hbeta⟩)
    (isPrin_theta k _) hxi heta

end ThetaWNoteD

end OrdinalAnalysis
