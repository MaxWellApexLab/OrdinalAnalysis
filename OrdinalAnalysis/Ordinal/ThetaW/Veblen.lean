/-
  The multi-level syntactic Veblen function `φ_k`.

  Source: A. Freund, arXiv:2204.09321, Definition 7.6: `φ_ρ(β) := ϑ(Ω·ρ + β)` (the one-level
  system has a single `Ω`), used in Lemma 7.7/Theorem 7.8 for predicative cut elimination.  The multi-level analogue is `φ_k(ρ, β) :=
  ϑ_k(Ω_{k+1}·ρ + β)`: this row is new content (no `φ` exists anywhere in the repository — the
  one-level system `Ordinal/Theta/*` has no Veblen function either, only `ω^·`, `ω·`, `+`).

  **`Ω_{k+1}·ρ`, syntactically.**  `Ω_{k+1} = ω^{Ω_{k+1}}` is additively indecomposable (a fixed
  point of `ω^·`, `ThetaWNoteD.omegaPow_eq_self_iff`), and standard ordinal arithmetic gives
  `ω^ξ · ω^η = ω^{ξ+η}`; so for `ρ` in Cantor normal form `ω^{ρ₀} + ⋯ + ω^{ρ_{n-1}}`, left
  distributivity gives `Ω_{k+1}·ρ = ω^{Ω_{k+1}+ρ₀} + ⋯ + ω^{Ω_{k+1}+ρ_{n-1}}`: exactly `ρ`'s
  Cantor exponents mapped by `Ω_{k+1} + ·`, one level up from `Theta/Arith.lean`'s `ω · α`
  (which maps them by `1 + ·`, since `ω = ω^1`).  The definition below (`omegaAdd`,
  `omegaMulOmega`) is `Theta/Arith.lean`'s `onePlus`/`omegaMul` verbatim with `sum []` (`= 0`)
  replaced by `Omega k`; this is *syntactic*, exactly as the rest of the file is not shown to
  denote true ordinal multiplication (no operation in `ThetaW/*` is shown to denote an ordinal
  at all — `ThetaW/Dom`'s docstrings mark every value as "intended").

  **The domain side condition.**  `ϑ_k` needs `Dom arg ∧ ∀ x ∈ G_k(arg), x < arg`
  (`ThetaW/Dom.dom_theta_iff`); `G_k` collects the *arguments* of `ϑ_j`-subterms with `j > k`
  reached through sums (never through a `ϑ_j` with `j ≤ k`, which is opaque to `G_k` — in
  particular `G_k` does not care how large an `Ω_j` is, only about `ϑ_j`, `j > k`).  So `G_k`
  vanishing on `arg` is a much weaker condition than `arg` itself being small; the theorem below
  (`dom_phi_of_lt`) shows it holds whenever `ρ, β ≺ Ω_{k+1}`, matching the earlier remark that `φ_k` is
  domain-safe there, and that it is *not* automatic for general `ρ, β`.

  **What is proved, and what is not.**  `φ_k` itself (`phi`), its normal form (`nf_phi`), the
  domain side condition (`dom_phi_of_lt`, the central aim of this file), and the
  monotonicity of its *argument* in `β` (`phiArg_lt_phiArg_of_lt`, safe: ordinary
  right-monotonicity of `+`, already in `ThetaW/Arith`).  **Not** attempted: `φ_k(ρ, β) ≺
  φ_k(ρ, β')` for `β ≺ β'` (the order-preservation half of Freund's Lemma 7.7/Def 7.6, and the
  bulk of its content) needs the general `ϑ_k α ≺ ϑ_k β` clause with `E_k`, since
  `Ω_{k+1}·ρ + β` sits *above* `Ω_{k+1}` (unlike every other `ϑ_k`-application already proved
  safe in `ThetaW/Dom`, all of whose arguments are `≺ Ω_{k+1}`) — computing `E_k` of it requires
  tracking exactly which `ϑ_j`-subterms of `ρ, β` survive at level `k`, which is a substantial
  independent argument (the design note estimates 300–450 lines for this row alone) and is left
  for a dedicated pass, not attempted here to avoid an under-verified order claim.
-/
import OrdinalAnalysis.Ordinal.ThetaW.Arith

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWTerm

/-! ### `Ω_{k+1} + ·` on terms, for `Ω_{k+1} · α` -/

/-- The term `Ω_{k+1} + e`, used entrywise for `Ω_{k+1} · α` below: `Theta/Arith.lean`'s
`onePlus` (`1 + e`) with `sum []` replaced by `Omega k`. -/
def omegaAdd (k : ℕ) (e : ThetaWTerm) : ThetaWTerm := ofList (addL [Omega k] (toList e))

theorem NF.omegaAdd {k : ℕ} {e : ThetaWTerm} (h : NF e) : NF (omegaAdd k e) :=
  nf_ofList_iff.mpr (CNF.addL ⟨by simp, List.pairwise_singleton _ _⟩ h.cnf_toList)

/-- `Ω_{k+1} + ·` preserves `Dom`: its exponents are `Ω_{k+1}` (`Dom` trivially) and the
exponents of `e`, which are `Dom` since `e` is. -/
theorem Dom.omegaAdd {k : ℕ} {e : ThetaWTerm} (h : Dom e) : Dom (omegaAdd k e) :=
  dom_ofList_iff.mpr (fun x hx => (mem_addL hx).elim
    (fun hx' => by rw [List.mem_singleton] at hx'; exact hx' ▸ dom_Omega k)
    (fun hx' => h.of_mem_toList hx'))

theorem omegaAdd_lt_omegaAdd {k : ℕ} {e e' : ThetaWTerm} (he : NF e) (he' : NF e') (h : e < e') :
    omegaAdd k e < omegaAdd k e' := by
  unfold omegaAdd
  rw [ofList_lt_ofList]
  refine addL_lt_addL_right (List.pairwise_singleton _ _) ?_
  rwa [← ofList_lt_ofList, ofList_toList he, ofList_toList he']

theorem omegaAdd_le_omegaAdd {k : ℕ} {e e' : ThetaWTerm} (he : NF e) (he' : NF e') (h : e ≤ e') :
    omegaAdd k e ≤ omegaAdd k e' := by
  rcases h with h | rfl
  · exact Or.inl (omegaAdd_lt_omegaAdd he he' h)
  · exact le_refl' _

/-! ### `G_k` vanishes on a term below `Ω_{k+1}`, and is preserved by `Ω_{k+1} + ·` and `+` -/

/-- If `G_k` vanishes on every entry of a list, it vanishes on their sum. -/
theorem G_sum_eq_nil_of_forall {k : ℕ} {xs : List ThetaWTerm} (h : ∀ x ∈ xs, G k x = []) :
    G k (sum xs) = [] := by
  induction xs with
  | nil => exact G_nil k
  | cons x xs ih =>
    rw [G_cons, h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem x hy))]
    rfl

/-- `G_k` vanishes on a normal term below `Ω_{k+1}`: `G_k` only ever picks up arguments of
`ϑ_j`-subterms with `j > k`, and every principal subterm reached through the (non-increasing)
Cantor-sum structure of a term `≺ Ω_{k+1}` is itself `≺ Ω_{k+1}`, hence any `ϑ_j` among them has
`j ≤ k` (`theta_lt_Omega_iff`) — so none of them contributes. -/
theorem G_eq_nil_of_lt_Omega {k : ℕ} : ∀ {t : ThetaWTerm}, NF t → t < Omega k → G k t = []
  | Omega j, _, _ => G_Omega k j
  | theta j a, _, h => G_theta_of_le ((theta_lt_Omega_iff j k a).mp h) a
  | sum xs, ht, h => by
      refine G_sum_eq_nil_of_forall (fun x hx => ?_)
      have hxnf : NF x := ht.of_mem hx
      have hxlt : x < Omega k := by
        rcases xs with _ | ⟨y, ys⟩
        · cases hx
        · have hy : y < Omega k := (cons_lt_Omega_iff k y ys).mp h
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hy
          · exact lt_of_le_of_lt' (ht.desc.le_head x (List.mem_cons_of_mem y hx')) hy
      exact G_eq_nil_of_lt_Omega hxnf hxlt
termination_by t => l t
decreasing_by exact l_lt_of_mem hx

/-- If `G_k` vanishes on a normal term, it vanishes on every one of its Cantor exponents. -/
theorem G_eq_nil_of_mem_toList {k : ℕ} {e : ThetaWTerm} (he : NF e) (h : G k e = [])
    {y : ThetaWTerm} (hy : y ∈ toList e) : G k y = [] := by
  by_contra hne
  obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ hne
  have hmem : g ∈ G k (ofList (toList e)) := mem_G_ofList.mpr ⟨y, hy, hg⟩
  rw [ofList_toList he, h] at hmem
  exact (List.not_mem_nil hmem)

/-- `G_k` vanishes on `Ω_{k+1} + e` whenever it vanishes on the normal term `e`: the exponents
of `Ω_{k+1} + e` are `Ω_{k+1}` itself (`G_k` always vanishes there) and the exponents of `e`
(`G_k` vanishes there by `G_eq_nil_of_mem_toList`). -/
theorem G_omegaAdd_eq_nil {k : ℕ} {e : ThetaWTerm} (he : NF e) (h : G k e = []) :
    G k (omegaAdd k e) = [] := by
  unfold omegaAdd
  rw [List.eq_nil_iff_forall_not_mem]
  intro g hg
  rw [mem_G_ofList] at hg
  obtain ⟨x, hx, hgx⟩ := hg
  rcases mem_addL hx with hx' | hx'
  · rw [List.mem_singleton] at hx'
    rw [hx', G_Omega] at hgx
    exact (List.not_mem_nil hgx)
  · rw [G_eq_nil_of_mem_toList he h hx'] at hgx
    exact (List.not_mem_nil hgx)

/-- `G_k` vanishes on `ofList (L.map (Ω_{k+1} + ·))` whenever it vanishes on every entry of
`L`. -/
theorem G_ofList_map_omegaAdd_eq_nil {k : ℕ} {L : List ThetaWTerm}
    (hL : ∀ y ∈ L, NF y ∧ G k y = []) : G k (ofList (L.map (omegaAdd k))) = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro g hg
  rw [mem_G_ofList] at hg
  obtain ⟨z, hz, hgz⟩ := hg
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
  obtain ⟨heNF, heG⟩ := hL e he
  rw [G_omegaAdd_eq_nil heNF heG] at hgz
  exact (List.not_mem_nil hgz)

/-- `G_k` vanishes on `ofList (addL (toList x) (toList y))` (the term-level shape of
`ThetaWNoteD`'s ordinal sum) whenever it vanishes on the normal terms `x` and `y`. -/
theorem G_add_eq_nil {k : ℕ} {x y : ThetaWTerm} (hx : NF x) (hy : NF y)
    (hgx : G k x = []) (hgy : G k y = []) :
    G k (ofList (addL (toList x) (toList y))) = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro g hg
  rw [mem_G_ofList] at hg
  obtain ⟨z, hz, hgz⟩ := hg
  rcases mem_addL hz with hz' | hz'
  · rw [G_eq_nil_of_mem_toList hx hgx hz'] at hgz; exact (List.not_mem_nil hgz)
  · rw [G_eq_nil_of_mem_toList hy hgy hz'] at hgz; exact (List.not_mem_nil hgz)

end ThetaWTerm

/-! ### `Ω_{k+1} · ρ` on `ThetaWNoteD` -/

namespace ThetaWNoteD

open ThetaWTerm

/-- `Ω_{k+1} · ρ`: every Cantor exponent of `ρ` is replaced by `Ω_{k+1} + ·`
(`Theta/Arith.lean`'s `ω · α`, one level up: see the module docstring). -/
def omegaMulOmega (k : ℕ) (a : ThetaWNoteD) : ThetaWNoteD :=
  ofEntries (a.entries.map (ThetaWTerm.omegaAdd k))
    ⟨fun x hx => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        exact ((cnf_entries a).nf he).omegaAdd,
      List.pairwise_map.mpr ((sorted_entries a).imp_of_mem fun hx hy h =>
        omegaAdd_le_omegaAdd ((cnf_entries a).nf hy) ((cnf_entries a).nf hx) h)⟩
    (fun x hx => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        exact Dom.omegaAdd (dom_entries a e he))

@[simp] theorem entries_omegaMulOmega (k : ℕ) (a : ThetaWNoteD) :
    (omegaMulOmega k a).entries = a.entries.map (ThetaWTerm.omegaAdd k) :=
  entries_ofEntries _ _ _

/-- `Ω_{k+1} · ·` preserves `Dom` (by construction; stated separately as required). -/
theorem dom_omegaMulOmega (k : ℕ) (a : ThetaWNoteD) : Dom (omegaMulOmega k a).1 :=
  (omegaMulOmega k a).2.2

theorem omegaMulOmega_lt_omegaMulOmega {k : ℕ} {a b : ThetaWNoteD} (h : a < b) :
    omegaMulOmega k a < omegaMulOmega k b := by
  rw [lt_iff_entries, entries_omegaMulOmega, entries_omegaMulOmega]
  exact sum_map_lt_sum_map (fun hx hy h => omegaAdd_lt_omegaAdd hx hy h)
    (cnf_entries a).1 (cnf_entries b).1 (lt_iff_entries.mp h)

theorem omegaMulOmega_zero (k : ℕ) : omegaMulOmega k zero = zero := ext_entries (by simp)

/-- `G_k` vanishes on `Ω_{k+1} · ρ` whenever it vanishes on `ρ` (term-level statement, feeding
`dom_phi_of_lt` below). -/
theorem G_omegaMulOmega_eq_nil {k : ℕ} {a : ThetaWNoteD} (h : ThetaWTerm.G k a.1 = []) :
    ThetaWTerm.G k (omegaMulOmega k a).1 = [] := by
  have h1 : (omegaMulOmega k a).1 = ofList (a.entries.map (ThetaWTerm.omegaAdd k)) := rfl
  rw [h1]
  exact G_ofList_map_omegaAdd_eq_nil
    (fun y hy => ⟨(cnf_entries a).nf hy, G_eq_nil_of_mem_toList a.2.1 h hy⟩)

/-! ### `φ_k(ρ, β) := ϑ_k(Ω_{k+1}·ρ + β)` (Freund, Definition 7.6, one level up) -/

/-- The argument `Ω_{k+1}·ρ + β` of `φ_k`. -/
def phiArg (k : ℕ) (rho beta : ThetaWNoteD) : ThetaWNoteD := omegaMulOmega k rho + beta

/-- `φ_k(ρ, β) := ϑ_k(Ω_{k+1}·ρ + β)`, as a raw term: `ϑ_k` needs a domain side condition
(`dom_phi_of_lt` below) that is not automatic in `ρ, β` (the domain of `ThetaWTerm.theta`,
`ThetaW/Dom.dom_theta_iff`, is a genuine restriction), so `φ_k` itself lands in `ThetaWTerm`,
not in `ThetaWNoteD` — exactly as `ThetaW/Dom` builds `cTerm`/`c` and `theta0Omega` before
bundling them, and as `Theta/Arith.lean`'s unconditional `theta` combinator has no analogue
here (see the module docstring of `ThetaW/Arith.lean`). -/
def phi (k : ℕ) (rho beta : ThetaWNoteD) : ThetaWTerm := ThetaWTerm.theta k (phiArg k rho beta).1

theorem nf_phi (k : ℕ) (rho beta : ThetaWNoteD) : NF (phi k rho beta) :=
  (nf_theta_iff k _).mpr (phiArg k rho beta).2.1

/-- **The domain side condition of `φ_k`** (the central aim of this file): `ρ, β ≺
Ω_{k+1}` puts `G_k` of the argument `Ω_{k+1}·ρ + β` at `∅` (`G_k` is insensitive to `Ω_j`'s of
any size, so `Ω_{k+1}·ρ` contributes nothing new to it, and `β ≺ Ω_{k+1}` alone makes `G_k(β) =
∅` by `G_eq_nil_of_lt_Omega`), hence `ϑ_k(Ω_{k+1}·ρ + β)` is in the domain
(`ThetaW/Dom.dom_theta_of_G_nil`). -/
theorem dom_phi_of_lt {k : ℕ} {rho beta : ThetaWNoteD} (hrho : rho < Omega k)
    (hbeta : beta < Omega k) : Dom (phi k rho beta) := by
  apply dom_theta_of_G_nil (phiArg k rho beta).2.2
  have hgr : G k rho.1 = [] := G_eq_nil_of_lt_Omega rho.2.1 hrho
  have hgb : G k beta.1 = [] := G_eq_nil_of_lt_Omega beta.2.1 hbeta
  have hgm : G k (omegaMulOmega k rho).1 = [] := G_omegaMulOmega_eq_nil hgr
  have heq : (phiArg k rho beta).1 =
      ofList (addL (toList (omegaMulOmega k rho).1) (toList beta.1)) := rfl
  rw [heq]
  exact G_add_eq_nil (omegaMulOmega k rho).2.1 beta.2.1 hgm hgb

/-- The argument of `φ_k` is strictly monotone in `β` (fixed `ρ`): the safe half of
`Theta/Arith.lean`-style monotonicity, since ordinal `+` is only right-strict-monotone in
general. -/
theorem phiArg_lt_phiArg_of_lt {k : ℕ} (rho : ThetaWNoteD) {beta beta' : ThetaWNoteD}
    (h : beta < beta') : phiArg k rho beta < phiArg k rho beta' :=
  add_lt_add_left _ h

theorem beta_le_phiArg (k : ℕ) (rho beta : ThetaWNoteD) : beta ≤ phiArg k rho beta :=
  le_add_left _ beta

end ThetaWNoteD

end OrdinalAnalysis
