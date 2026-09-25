/-
  The hulls `C^α_k(β)` and the operators `H_{k,α}` on the multi-level ϑ-notation.

  Source: A. Freund, arXiv:2204.09321, Definition 3.8, Proposition 3.9, Definition 3.10,
  Proposition 3.11, Definition 5.4, Exercise 5.5 (Buchholz, *A new system of proof-theoretic
  ordinal functions*, Ann. Pure Appl. Logic 32 (1986), Lemma 4.7 (𝒜1)-(𝒜4) of the companion
  1992 paper *A simplified version of local predicativity*), ported level by level to
  `ThetaWNoteD` exactly as `Ordinal/Theta/Hull.lean` does for the one-level system; see
  `Ordinal/Theta/Hull.lean` for the un-generalized proofs this file follows line by line.

  **The one new design decision**: the single clause
  `CsetT.ofTheta` of the one-level system (closing the hull under `ϑ` on arguments `≺ α`) is
  split into three, following exactly how the level-`k` coefficient set `E_k` already treats a
  collapse `ϑ_j ξ` (`ThetaW/Basic.lean`, `E_theta_of_le`/`E_theta_of_lt`):
  * `ofThetaLow` (`j < k`): `ϑ_j ξ` is admitted to the hull **unconditionally**, for every raw
    `ξ`. `E_k` stops at such a term (`E_k(ϑ_j ξ) = {ϑ_j ξ}`, opaque), so it plays the role of an
    already-built atom from a "lower", presupposed level, exactly as in G. Wilken's simultaneous
    system (arXiv:2410.15953, Definition 2.7): the hull `C̄_k` is built on top of the completed
    systems of level `< k`.
  * `ofThetaHigh` (`k < j`): `ϑ_j ξ` is admitted **transparently**, exactly when the hull
    already contains `ξ`. `E_k` passes through such a term (`E_k(ϑ_j ξ) = E_k(ξ)`), and the
    hull membership must pass through with it, for Proposition 3.9's `iff_E` half.
  * `ofThetaOwn` (`j = k`): the one-level clause verbatim — `ξ ≺ α` and (new, mandatory here)
    `Dom (ϑ_k ξ)`, since `ThetaWTerm.theta` is not an unconditional combinator on `ThetaWNoteD`
    (`ThetaW/Arith.lean`'s module docstring; `ThetaW/Dom.dom_theta_iff`).
  This is *not* literally Wilken's Definition 2.7 (closure under `ϑ_j` only for `j ≥ k`); it is
  forced by the second half of Proposition 3.9 below (`CsetT_of_lt_theta`, "every `δ ≺ ϑ_k α`
  lies in the hull"), which needs arbitrary `ϑ_j ξ` with `j < k` admitted freely — such a term
  lies below `Ω_k` and below every `ϑ_k`-term **by position alone**, regardless of `ξ`
  (`theta_lt_theta_of_lt_level`), so admitting it freely can never make anything wrongly small,
  and the alternative (closing under `ϑ_j`, `j < k`, only on bounded/domain-safe arguments,
  literally as Wilken states it) makes the "every small term is in the hull" direction fail for
  a `ϑ_j ξ` with `ξ` outside that bound.

  Two more genuine (not merely notational) additions over the one-level file, both consequences
  of `ThetaWNoteD` carrying `Dom`:
  * `theta_isLeast`, `theta_mem_Hop`, `theta_lt_theta_of_mem_Hop` take an explicit
    `Dom (theta k _)` hypothesis at the point of application (not automatic, unlike the one-level
    file's unconditional `ThetaNote.theta`);
  * `add_omegaPow_mem_Hop`/`theta_add_omegaPow_mem_Hop` (the Theorem 6.7 shape) need the extra
    hypotheses `a < Omega k`, `b < Omega k` to get `Dom (theta k (a + omegaPow b))`, by the same
    argument as `ThetaW/Veblen.lean`'s `dom_phi_of_lt`.

  **A design question raised mid-development and answered here, with counterexamples**: could `Cset`/`Hop`/`Nice`/`HullHyp` be made
  level-free (one hull `C(α,β)` closed under every `ϑ_j`, `j` unrestricted, uniformly bounded by
  `α`, as in Buchholz 1992 Definition 4.2 literally), with the level entering only as a parameter
  of individual lemmas (Prop 3.9/3.11) rather than of the operator?  Answer: the general
  "closed under the arithmetic" direction (Exercise 5.5) can be made level-free this way, using a
  *new*, level-independent, always-atomic coefficient function in place of `E_k` — but the
  *minimality* half of Prop 3.9 (`CsetT_of_lt_theta`/`theta_isLeast`, the file's own headline
  `ϑ_k α = min{...}`) then genuinely **fails**: `ThetaW/Basic`'s position-first order clause gives
  `ϑ_j γ ≺ ϑ_κ α` for *every* `γ` whenever `j < κ`, so for `κ` large, `j` small and `γ` an
  unrelated large term (e.g. `γ = Ω_{100}`), `ϑ_j γ ≺ ϑ_κ α` holds by position while `ϑ_j γ` is
  not constructible in *any* hull uniformly bounded by `α`.  This is a counterexample to the
  theorem, not a proof gap, and it is exactly what this file's `ofThetaLow` clause (free
  admission of every `j < k` term) is for.  Similarly, replacing
  `theta_add_omegaPow_mem_Hop`'s `a, b < Omega k` hypothesis by a `HullHyp`-derived one fails: on
  a related question, `Dom α` does not imply `Dom (theta k α)` for an unrelated level `k`
  (already on record as `ThetaW/Dom.theta1_Omega5_lt_Omega1` et al.); concretely
  `α := theta 5 (Omega 10)` is domain-safe, yet `G 3 α = {Omega 10}` and `Omega 10 ⊀ α`, so
  `Dom (theta 3 α)` fails, with no `Hop`/`HullHyp`-only argument found to exclude this shape of
  `α`.  Both the per-level design and the `a, b < Omega k` bound below are therefore kept as is.
-/
import OrdinalAnalysis.Ordinal.ThetaW.Veblen
import Mathlib.Order.Bounds.Defs
import Mathlib.Data.Set.Lattice

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWTerm

/-! ### Coefficients of the Cantor exponents, level `k` -/

/-- `E_k(α)` is the union of the `E_k(e)` over the Cantor exponents `e` of `α`. -/
theorem mem_E_iff_toList_hull {k : ℕ} {t g : ThetaWTerm} :
    g ∈ E k t ↔ ∃ e ∈ toList t, g ∈ E k e := by
  cases t with
  | Omega j => simp [toList, E_Omega]
  | theta j a => simp [toList]
  | sum xs => exact mem_E_sum

/-- `E_k(1 + α) ⊆ E_k(α)`. -/
theorem mem_E_of_mem_E_onePlus_hull {k : ℕ} {e g : ThetaWTerm} (h : g ∈ E k (onePlus e)) :
    g ∈ E k e := by
  unfold onePlus at h
  obtain ⟨x, hx, hg⟩ := mem_E_ofList.mp h
  rcases mem_addL hx with hx | hx
  · rw [List.mem_singleton.mp hx] at hg; simp at hg
  · exact mem_E_iff_toList_hull.mpr ⟨x, hx, hg⟩

/-! ### The hulls `C^α_k(β)` on raw terms -/

/-- The generating clauses of `C^α_k(β)` (Freund, Definition 3.8, per level): see the module
docstring for the three-way split of the collapsing clause. -/
inductive CsetT (k : ℕ) (a b : ThetaWTerm) : ThetaWTerm → Prop
  /-- Clause (i): `Ω_j ∈ C^α_k(β)` for every level `j`. -/
  | ofOmega (j : ℕ) : CsetT k a b (Omega j)
  /-- Clause (i): `γ ∈ C^α_k(β)` for `γ ≺ β`. -/
  | ofLt {g : ThetaWTerm} : g < b → CsetT k a b g
  /-- `ϑ_j ξ ∈ C^α_k(β)` unconditionally for `j < k` (an atom from a lower, presupposed level:
  `E_k` never looks inside it). -/
  | ofThetaLow {j : ℕ} (hj : j < k) (g : ThetaWTerm) : CsetT k a b (theta j g)
  /-- `ϑ_j ξ ∈ C^α_k(β)` whenever `ξ ∈ C^α_k(β)`, for `j > k` (`E_k` looks through it). -/
  | ofThetaHigh {j : ℕ} (hj : k < j) {g : ThetaWTerm} : CsetT k a b g → CsetT k a b (theta j g)
  /-- Clause (ii), the hull's own level: `γ ∈ C^α_k(β)`, `γ ≺ α`, and `ϑ_k γ` is domain-safe
  give `ϑ_k γ ∈ C^α_k(β)`. -/
  | ofThetaOwn {g : ThetaWTerm} : CsetT k a b g → g < a → Dom (theta k g) →
      CsetT k a b (theta k g)
  /-- Clause (iii): `⟨γ₀, …, γ_{n-1}⟩ ∈ C^α_k(β)` when every `γ_i ∈ C^α_k(β)`. -/
  | ofSum {xs : List ThetaWTerm} : (∀ x ∈ xs, CsetT k a b x) → CsetT k a b (sum xs)

/-- Proposition 3.9, right to left, level `k`: `E_k(γ) ⊆ C^α_k(β)` gives `γ ∈ C^α_k(β)`. -/
theorem CsetT.of_E {k : ℕ} {a b : ThetaWTerm} : ∀ {g : ThetaWTerm},
    (∀ d ∈ E k g, CsetT k a b d) → CsetT k a b g
  | Omega j, _ => .ofOmega j
  | theta j a', h => by
      rcases lt_trichotomy j k with hj | rfl | hj
      · exact .ofThetaLow hj a'
      · exact h _ (by simp [E_theta_of_le (le_refl j)])
      · exact .ofThetaHigh hj (CsetT.of_E (fun d hd => h d (by rwa [E_theta_of_lt hj])))
  | sum xs, h => .ofSum fun x hx => CsetT.of_E (fun d hd => h d (mem_E_of_mem hx hd))
termination_by g => l g
decreasing_by
  · simp
  · exact l_lt_of_mem hx

/-- Proposition 3.9, left to right, level `k`: for normal `γ`, `γ ∈ C^α_k(β)` gives
`E_k(γ) ⊆ C^α_k(β)`. -/
theorem CsetT.E_sub {k : ℕ} {a b g : ThetaWTerm} (h : CsetT k a b g) (hg : NF g) :
    ∀ d ∈ E k g, CsetT k a b d := by
  revert hg
  induction h with
  | ofOmega j => intro _ d hd; simp at hd
  | ofLt hlt =>
    intro hg d hd
    exact .ofLt (lt_of_le_of_lt' (le_of_mem_E hg hd) hlt)
  | ofThetaLow hj g' =>
    intro _ d hd
    rw [E_theta_of_le hj.le] at hd
    simp only [List.mem_singleton] at hd
    subst hd
    exact .ofThetaLow hj g'
  | ofThetaHigh hj hc ih =>
    intro hg d hd
    rw [E_theta_of_lt hj] at hd
    exact ih hg.theta_arg d hd
  | ofThetaOwn hc hlt hdom _ih =>
    intro _ d hd
    rw [E_theta_of_le (le_refl k)] at hd
    simp only [List.mem_singleton] at hd
    subst hd
    exact .ofThetaOwn hc hlt hdom
  | ofSum _ ih =>
    intro hg d hd
    obtain ⟨x, hx, hdx⟩ := mem_E_sum.mp hd
    exact ih x hx (hg.of_mem hx) d hdx

theorem CsetT.iff_E {k : ℕ} {a b g : ThetaWTerm} (hg : NF g) :
    CsetT k a b g ↔ ∀ d ∈ E k g, CsetT k a b d :=
  ⟨fun h => h.E_sub hg, CsetT.of_E⟩

/-- Proposition 3.9, first half of the proof of the minimum, level `k`:
`C^α_k(ϑ_k α) ∩ Ω_k ≺* ϑ_k α`, by induction on the length. -/
theorem lt_theta_of_CsetT_theta {k : ℕ} {a : ThetaWTerm} : ∀ {d : ThetaWTerm}, NF d →
    CsetT k a (theta k a) d → d < Omega k → d < theta k a
  | Omega j, _, _, hΩ => (Omega_lt_theta_iff j k a).mpr ((Omega_lt_Omega_iff j k).mp hΩ)
  | theta j d', hn, hc, hΩ => by
      have hjk : j ≤ k := (theta_lt_Omega_iff j k d').mp hΩ
      rcases Nat.lt_or_eq_of_le hjk with hj | hj
      · cases hc with
        | ofLt h => exact h
        | ofThetaLow hj' _ => exact theta_lt_theta_of_lt_level d' a hj
        | ofThetaHigh hj' _ => omega
        | ofThetaOwn _ _ _ => omega
      · subst hj
        cases hc with
        | ofLt h => exact h
        | ofThetaLow hj' _ => omega
        | ofThetaHigh hj' _ => omega
        | ofThetaOwn h1 h2 h3 =>
          refine theta_lt_theta_of_lt h2 fun g hg => ?_
          exact lt_theta_of_CsetT_theta ((nf_theta_iff j d').mp hn |>.of_mem_E hg)
            (h1.E_sub ((nf_theta_iff j d').mp hn) g hg) (lt_Omega_of_mem_E hg)
  | sum [], _, _, _ => nil_lt_theta k a
  | sum (x :: xs), hn, hc, hΩ => by
      cases hc with
      | ofLt h => exact h
      | ofSum h =>
        rw [cons_lt_theta_iff]
        exact lt_theta_of_CsetT_theta (hn.of_mem List.mem_cons_self) (h x List.mem_cons_self)
          ((cons_lt_Omega_iff k x xs).mp hΩ)
termination_by d => l d
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · simp; omega

/-- Proposition 3.9, second half of the proof of the minimum, level `k`: if
`C^α_k(γ) ∩ Ω_k ≺* γ` and `α ∈ C^α_k(γ)`, then every normal domain `δ ≺ ϑ_k α` lies in
`C^α_k(γ)`, by induction on the length. -/
theorem CsetT_of_lt_theta {k : ℕ} {a c : ThetaWTerm} (ha : NF a) (hda : Dom a)
    (hc : ∀ d, NF d → Dom d → CsetT k a c d → d < Omega k → d < c) (hac : CsetT k a c a) :
    ∀ {d : ThetaWTerm}, NF d → Dom d → d < theta k a → CsetT k a c d
  | Omega j, _, _, _ => .ofOmega j
  | theta j d', hn, hd, h => by
      have hjk : j ≤ k := by
        by_contra hjk
        exact absurd h (not_theta_lt_theta_of_lt_level d' a (Nat.lt_of_not_le hjk))
      rcases Nat.lt_or_eq_of_le hjk with hj | hj
      · exact .ofThetaLow hj d'
      · subst hj
        rcases (theta_lt_theta_iff j d' a).mp h with ⟨h1, h2⟩ | ⟨g, hg, hle⟩
        · have hdd' : Dom d' := hd.theta_arg
          refine .ofThetaOwn (CsetT.of_E fun g hg => ?_) h1 ?_
          · exact CsetT_of_lt_theta ha hda hc hac ((nf_theta_iff j d').mp hn |>.of_mem_E hg)
              (hdd'.of_mem_E hg) (h2 g hg)
          · exact hd
        · have hgd : Dom g := hda.of_mem_E hg
          have hgn : NF g := ha.of_mem_E hg
          exact .ofLt (lt_of_le_of_lt' hle (hc g hgn hgd (hac.E_sub ha g hg) (lt_Omega_of_mem_E hg)))
  | sum [], _, _, _ => .ofSum (by simp)
  | sum (y :: ys), hn, hd, h => by
      refine .ofSum fun x hx => ?_
      have hle : x ≤ y := hn.desc.le_head x hx
      have hxn : NF x := hn.of_mem hx
      have hxd : Dom x := hd.of_mem hx
      exact CsetT_of_lt_theta ha hda hc hac hxn hxd
        (lt_of_le_of_lt' hle ((cons_lt_theta_iff k y a ys).mp h))
termination_by d => l d
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · exact l_lt_of_mem hx

end ThetaWTerm

namespace ThetaWNoteD

open ThetaWTerm

/-! ### Coefficient sets of notations, level `k` -/

/-- The set `E_k(α)` of `ThetaW/Basic`, as a set of notations. -/
def Ehull (k : ℕ) (a : ThetaWNoteD) : Set ThetaWNoteD := {g | g.1 ∈ E k a.1}

theorem mem_Ehull {k : ℕ} {a g : ThetaWNoteD} : g ∈ Ehull k a ↔ g.1 ∈ E k a.1 := Iff.rfl

theorem mem_Ehull_iff_entries_hull {k : ℕ} {a g : ThetaWNoteD} :
    g ∈ Ehull k a ↔ ∃ e ∈ a.entries, g.1 ∈ E k e :=
  mem_E_iff_toList_hull

/-- `ϑ_k α`, taking its domain proof explicitly: `ThetaWNoteD` has no unconditional `theta`
combinator (`ThetaW/Arith.lean`'s module docstring), so every application of `ϑ_k` on
`ThetaWNoteD` in this file threads the side condition through. -/
def thetaD (k : ℕ) (a : ThetaWNoteD) (hdom : Dom (ThetaWTerm.theta k a.1)) : ThetaWNoteD :=
  ⟨ThetaWTerm.theta k a.1, (ThetaWTerm.nf_theta_iff k a.1).mpr a.2.1, hdom⟩

@[simp] theorem thetaD_val (k : ℕ) (a : ThetaWNoteD) (hdom : Dom (ThetaWTerm.theta k a.1)) :
    (thetaD k a hdom).1 = ThetaWTerm.theta k a.1 := rfl

theorem thetaD_lt_Omega (k : ℕ) (a : ThetaWNoteD) (hdom : Dom (ThetaWTerm.theta k a.1)) :
    thetaD k a hdom < Omega k :=
  ThetaWTerm.theta_lt_Omega_self k a.1

/-! ### The hulls `C^α_k(β)` (Definition 3.8, level `k`) -/

/-- The set `C^α_k(β)` of `ThetaW/Hull.CsetT`. -/
def Cset (k : ℕ) (a b : ThetaWNoteD) : Set ThetaWNoteD := {g | CsetT k a.1 b.1 g.1}

theorem mem_Cset {k : ℕ} {a b g : ThetaWNoteD} : g ∈ Cset k a b ↔ CsetT k a.1 b.1 g.1 := Iff.rfl

/-- Clause (i): `Ω_j ∈ C^α_k(β)`, every level `j`. -/
theorem Omega_mem_Cset (k j : ℕ) (a b : ThetaWNoteD) : Omega j ∈ Cset k a b := CsetT.ofOmega j

/-- Clause (i): `γ ∈ C^α_k(β)` for `γ ≺ β`. -/
theorem mem_Cset_of_lt {k : ℕ} {a b g : ThetaWNoteD} (h : g < b) : g ∈ Cset k a b :=
  CsetT.ofLt h

/-- Clause (ii), the hull's own level: `γ ∈ C^α_k(β)`, `γ ≺ α`, `ϑ_k γ` domain-safe give
`ϑ_k γ ∈ C^α_k(β)`. -/
theorem theta_mem_Cset {k : ℕ} {a b g : ThetaWNoteD} (h : g ∈ Cset k a b) (hg : g < a)
    (hdom : Dom (ThetaWTerm.theta k g.1)) : thetaD k g hdom ∈ Cset k a b :=
  CsetT.ofThetaOwn h hg hdom

/-- Clause (iii): a sum `⟨γ₀, …, γ_{n-1}⟩` lies in `C^α_k(β)` when every `γ_i` does. -/
theorem sum_mem_Cset {k : ℕ} {a b g : ThetaWNoteD} {xs : List ThetaWTerm} (hg : g.1 = sum xs)
    (h : ∀ x : ThetaWNoteD, x.1 ∈ xs → x ∈ Cset k a b) : g ∈ Cset k a b := by
  rw [mem_Cset, hg]
  have hn : NF (sum xs) := hg ▸ g.2.1
  have hd : Dom (sum xs) := hg ▸ g.2.2
  exact CsetT.ofSum fun x hx => h ⟨x, hn.of_mem hx, hd.of_mem hx⟩ hx

/-! ### Proposition 3.9, level `k` -/

/-- Proposition 3.9, first part: `γ ∈ C^α_k(β) ⇔ E_k(γ) ⊆ C^α_k(β)`. -/
theorem mem_Cset_iff_Ehull_subset {k : ℕ} {a b g : ThetaWNoteD} :
    g ∈ Cset k a b ↔ Ehull k g ⊆ Cset k a b := by
  rw [mem_Cset, CsetT.iff_E g.2.1]
  constructor
  · intro h d hd
    exact h d.1 hd
  · intro h d hd
    exact h (a := ⟨d, g.2.1.of_mem_E hd, g.2.2.of_mem_E hd⟩) hd

/-- `α ∈ C^α_k(ϑ_k α)`. -/
theorem mem_Cset_theta_self {k : ℕ} (a : ThetaWNoteD) (hdom : Dom (ThetaWTerm.theta k a.1)) :
    a ∈ Cset k a (thetaD k a hdom) :=
  mem_Cset_iff_Ehull_subset.mpr fun _ hg => mem_Cset_of_lt (ThetaWTerm.lt_theta_of_mem_E hg)

/-- `C^α_k(ϑ_k α) ∩ Ω_k ≺* ϑ_k α`. -/
theorem lt_theta_of_mem_Cset {k : ℕ} {a d : ThetaWNoteD} (hdom : Dom (ThetaWTerm.theta k a.1))
    (hd : d ∈ Cset k a (thetaD k a hdom)) (hΩ : d < Omega k) : d < thetaD k a hdom :=
  ThetaWTerm.lt_theta_of_CsetT_theta d.2.1 hd hΩ

/-- Proposition 3.9, second part, level `k`:
`ϑ_k α = min {γ | C^α_k(γ) ∩ Ω_k ≺* γ and α ∈ C^α_k(γ)}`. -/
theorem theta_isLeast {k : ℕ} (a : ThetaWNoteD) (hdom : Dom (ThetaWTerm.theta k a.1)) :
    IsLeast {c : ThetaWNoteD | (∀ d ∈ Cset k a c, d < Omega k → d < c) ∧ a ∈ Cset k a c}
      (thetaD k a hdom) := by
  refine ⟨⟨fun d hd hΩ => lt_theta_of_mem_Cset hdom hd hΩ, mem_Cset_theta_self a hdom⟩, ?_⟩
  rintro c ⟨hc, hac⟩
  by_contra hlt
  have hlt : c < thetaD k a hdom := lt_of_not_ge hlt
  have hcC : c ∈ Cset k a c :=
    ThetaWTerm.CsetT_of_lt_theta a.2.1 a.2.2
      (fun d hdn hdd hdC hdΩ => hc ⟨d, hdn, hdd⟩ hdC hdΩ) hac c.2.1 c.2.2 hlt
  exact absurd (hc c hcC (lt_trans hlt (thetaD_lt_Omega k a hdom))) (lt_irrefl c)

/-! ### The operators `H_{k,α}` (Definition 3.10, level `k`) -/

/-- The operator `H_{k,α}` of Freund, Definition 3.10, level `k`:
`H_{k,α}(X) = ⋂ {C^γ_k(δ) | α ≺ γ and X ⊆ C^γ_k(δ)}`. -/
def Hop (k : ℕ) (a : ThetaWNoteD) (X : Set ThetaWNoteD) : Set ThetaWNoteD :=
  {x | ∀ c d : ThetaWNoteD, a < c → X ⊆ Cset k c d → x ∈ Cset k c d}

theorem mem_Hop {k : ℕ} {a x : ThetaWNoteD} {X : Set ThetaWNoteD} :
    x ∈ Hop k a X ↔ ∀ c d : ThetaWNoteD, a < c → X ⊆ Cset k c d → x ∈ Cset k c d := Iff.rfl

theorem Hop_eq_sInter (k : ℕ) (a : ThetaWNoteD) (X : Set ThetaWNoteD) :
    Hop k a X = ⋂₀ {S | ∃ c d : ThetaWNoteD, a < c ∧ X ⊆ Cset k c d ∧ S = Cset k c d} := by
  ext x
  simp only [Set.mem_sInter, Set.mem_ofPred_eq, mem_Hop]
  constructor
  · rintro h S ⟨c, d, hac, hX, rfl⟩
    exact h c d hac hX
  · intro h c d hac hX
    exact h _ ⟨c, d, hac, hX, rfl⟩

theorem Hop_eq_univ {k : ℕ} {a : ThetaWNoteD} {X : Set ThetaWNoteD}
    (h : ∀ c d : ThetaWNoteD, a < c → ¬ X ⊆ Cset k c d) : Hop k a X = Set.univ :=
  Set.eq_univ_of_forall fun _ c d hac hX => absurd hX (h c d hac)

theorem Hop_subset_Cset {k : ℕ} {a c d : ThetaWNoteD} {X : Set ThetaWNoteD} (hac : a < c)
    (hX : X ⊆ Cset k c d) : Hop k a X ⊆ Cset k c d :=
  fun _ hx => hx c d hac hX

/-! ### Proposition 3.11, level `k` -/

/-- Proposition 3.11 (a): `α ≺ β` gives `H_{k,α}(X) ⊆ H_{k,β}(X)`. -/
theorem Hop_subset_Hop {k : ℕ} {a b : ThetaWNoteD} (h : a < b) (X : Set ThetaWNoteD) :
    Hop k a X ⊆ Hop k b X :=
  fun _ hx c d hbc hX => hx c d (lt_trans h hbc) hX

theorem Hop_subset_Hop_of_le {k : ℕ} {a b : ThetaWNoteD} (h : a ≤ b) (X : Set ThetaWNoteD) :
    Hop k a X ⊆ Hop k b X := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact Hop_subset_Hop h X
  · exact le_rfl

/-- Proposition 3.11 (b): `α ∈ H_{k,β}(X)` and `α ≼ β` give `ϑ_k α ∈ H_{k,β}(X)` (given the
domain side condition on `ϑ_k α`, not automatic here). -/
theorem theta_mem_Hop {k : ℕ} {x b : ThetaWNoteD} {X : Set ThetaWNoteD} (hx : x ∈ Hop k b X)
    (hxb : x ≤ b) (hdom : Dom (ThetaWTerm.theta k x.1)) : thetaD k x hdom ∈ Hop k b X :=
  fun c d hbc hX => theta_mem_Cset (hx c d hbc hX) (lt_of_le_of_lt hxb hbc) hdom

/-- The hypothesis `X ⊆ ⋂ {C^γ_k(ϑ_k γ) | α ≺ γ}` of Proposition 3.11 (c) and Theorem 6.7,
level `k`.  Phrased directly (rather than via `⋂`) because `ϑ_k γ` needs an explicit domain
proof for every `γ`, not automatic here (`ThetaW/Arith.lean`'s module docstring). -/
def HullHyp (k : ℕ) (a : ThetaWNoteD) (X : Set ThetaWNoteD) : Prop :=
  ∀ c : ThetaWNoteD, a < c → ∀ hc : Dom (ThetaWTerm.theta k c.1), X ⊆ Cset k c (thetaD k c hc)

theorem HullHyp.subset_Cset {k : ℕ} {a c : ThetaWNoteD} {X : Set ThetaWNoteD} (h : HullHyp k a X)
    (hac : a < c) (hc : Dom (ThetaWTerm.theta k c.1)) : X ⊆ Cset k c (thetaD k c hc) :=
  h c hac hc

/-- The hypothesis passes to larger indices (`α ≺ η` in Theorem 6.7). -/
theorem HullHyp.mono {k : ℕ} {a b : ThetaWNoteD} {X : Set ThetaWNoteD} (h : HullHyp k a X)
    (hab : a ≤ b) : HullHyp k b X :=
  fun _c hbc hc => h.subset_Cset (lt_of_le_of_lt hab hbc) hc

/-- `H_{k,α}(X) ⊆ C^γ_k(ϑ_k γ)` for `α ≺ γ` (Theorem 6.7, via Definition 3.10). -/
theorem HullHyp.Hop_subset {k : ℕ} {a c : ThetaWNoteD} {X : Set ThetaWNoteD} (h : HullHyp k a X)
    (hac : a < c) (hc : Dom (ThetaWTerm.theta k c.1)) :
    Hop k a X ⊆ Cset k c (thetaD k c hc) :=
  Hop_subset_Cset hac (h.subset_Cset hac hc)

/-- `δ ∈ H_{k,α}(X)` and `δ ≺ Ω_k` give `δ ≺ ϑ_k γ` for `α ≺ γ` (Theorem 6.7, via
Proposition 3.9). -/
theorem HullHyp.lt_theta {k : ℕ} {a c d : ThetaWNoteD} {X : Set ThetaWNoteD} (h : HullHyp k a X)
    (hac : a < c) (hc : Dom (ThetaWTerm.theta k c.1)) (hd : d ∈ Hop k a X) (hΩ : d < Omega k) :
    d < thetaD k c hc :=
  lt_theta_of_mem_Cset hc (h.Hop_subset hac hc hd) hΩ

/-- The case of clause (V) in Theorem 6.7: `δ ∈ H_{k,α}(X)`, `δ ≺ Ω_k` and `γ ≺ δ` give the
hypothesis for `X ∪ {γ}`. -/
theorem HullHyp.union_singleton {k : ℕ} {a d g : ThetaWNoteD} {X : Set ThetaWNoteD}
    (h : HullHyp k a X) (hd : d ∈ Hop k a X) (hΩ : d < Omega k) (hgd : g < d) :
    HullHyp k a (X ∪ {g}) :=
  fun _c hac hc => Set.union_subset (h.subset_Cset hac hc)
    (Set.singleton_subset_iff.mpr (mem_Cset_of_lt (lt_trans hgd (h.lt_theta hac hc hd hΩ))))

/-- Proposition 3.11 (c): if `X ⊆ ⋂ {C^γ_k(ϑ_k γ) | α ≺ γ}`, then `α ≼ β ≺ γ` and
`β ∈ H_{k,α}(X)` give `ϑ_k β ≺ ϑ_k γ` (given domain side conditions on both collapses). -/
theorem theta_lt_theta_of_mem_Hop {k : ℕ} {base x y : ThetaWNoteD} {X : Set ThetaWNoteD}
    (hX : HullHyp k base X) (hbx : base ≤ x) (hxy : x < y) (hx : x ∈ Hop k base X)
    (hdomx : Dom (ThetaWTerm.theta k x.1)) (hdomy : Dom (ThetaWTerm.theta k y.1)) :
    thetaD k x hdomx < thetaD k y hdomy := by
  have h1 : thetaD k x hdomx ∈ Hop k x X :=
    theta_mem_Hop (Hop_subset_Hop_of_le hbx X hx) le_rfl hdomx
  have hXy : X ⊆ Cset k y (thetaD k y hdomy) := hX y (lt_of_le_of_lt hbx hxy) hdomy
  exact lt_theta_of_mem_Cset hdomy (h1 y (thetaD k y hdomy) hxy hXy) (thetaD_lt_Omega k x hdomx)

/-! ### Coefficient facts for the arithmetic, level `k` -/

@[simp] theorem Ehull_Omega_hull (k j : ℕ) : Ehull k (Omega j) = ∅ := by
  ext g; change g.1 ∈ ThetaWTerm.E k (ThetaWTerm.Omega j) ↔ False; simp

@[simp] theorem Ehull_zero_hull (k : ℕ) : Ehull k zero = ∅ := by
  ext g; change g.1 ∈ ThetaWTerm.E k (ThetaWTerm.sum []) ↔ False; simp

/-- `E_k(α + β) ⊆ E_k(α) ∪ E_k(β)`. -/
theorem Ehull_add_subset_hull (k : ℕ) (a b : ThetaWNoteD) :
    Ehull k (a + b) ⊆ Ehull k a ∪ Ehull k b := by
  intro g hg
  obtain ⟨e, he, hge⟩ := mem_Ehull_iff_entries_hull.mp hg
  rw [entries_add] at he
  rcases mem_addL he with he | he
  · exact Or.inl (mem_Ehull_iff_entries_hull.mpr ⟨e, he, hge⟩)
  · exact Or.inr (mem_Ehull_iff_entries_hull.mpr ⟨e, he, hge⟩)

/-- `E_k(α ⊕ β) ⊆ E_k(α) ∪ E_k(β)`. -/
theorem Ehull_nadd_subset_hull (k : ℕ) (a b : ThetaWNoteD) :
    Ehull k (nadd a b) ⊆ Ehull k a ∪ Ehull k b := by
  intro g hg
  obtain ⟨e, he, hge⟩ := mem_Ehull_iff_entries_hull.mp hg
  rw [entries_nadd] at he
  rcases mem_mergeL.mp he with he | he
  · exact Or.inl (mem_Ehull_iff_entries_hull.mpr ⟨e, he, hge⟩)
  · exact Or.inr (mem_Ehull_iff_entries_hull.mpr ⟨e, he, hge⟩)

/-- `E_k(ω^α) = E_k(α)`. -/
theorem Ehull_omegaPow_hull (k : ℕ) (a : ThetaWNoteD) : Ehull k (omegaPow a) = Ehull k a := by
  ext g
  rw [mem_Ehull_iff_entries_hull, entries_omegaPow]
  simp [mem_Ehull]

/-- `E_k(ω · α) ⊆ E_k(α)`. -/
theorem Ehull_omegaMul_subset_hull (k : ℕ) (a : ThetaWNoteD) :
    Ehull k (omegaMul a) ⊆ Ehull k a := by
  intro g hg
  obtain ⟨e, he, hge⟩ := mem_Ehull_iff_entries_hull.mp hg
  rw [entries_omegaMul] at he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  exact mem_Ehull_iff_entries_hull.mpr ⟨d, hd, mem_E_of_mem_E_onePlus_hull hge⟩

@[simp] theorem Ehull_one_hull (k : ℕ) : Ehull k one = ∅ := by
  rw [one, Ehull_omegaPow_hull, Ehull_zero_hull]

@[simp] theorem Ehull_ofNat_hull (k n : ℕ) : Ehull k (ofNat n) = ∅ := by
  ext g
  simp only [mem_Ehull_iff_entries_hull, entries_ofNat, Set.mem_empty_iff_false, iff_false]
  rintro ⟨e, he, hg⟩
  rw [List.eq_of_mem_replicate he] at hg
  simp at hg

theorem Ehull_succ_subset_hull (k : ℕ) (a : ThetaWNoteD) : Ehull k (succ a) ⊆ Ehull k a := by
  intro g hg
  rcases Ehull_nadd_subset_hull k a one hg with h | h
  · exact h
  · simp at h

/-! ### Operators (Definition 5.4), level `k` -/

/-- A closure operator (Freund, Definition 5.4): `X ⊆ H(X)`, and `X ⊆ H(Y)` gives
`H(X) ⊆ H(Y)`.  Level-independent. -/
def IsOperator (H : Set ThetaWNoteD → Set ThetaWNoteD) : Prop :=
  (∀ X, X ⊆ H X) ∧ ∀ X Y, X ⊆ H Y → H X ⊆ H Y

/-- A nice operator at level `k` (Freund, Definition 5.4): an operator with
`α ∈ H(X) ⇔ E_k(α) ⊆ H(X)`. -/
def Nice (k : ℕ) (H : Set ThetaWNoteD → Set ThetaWNoteD) : Prop :=
  IsOperator H ∧ ∀ (X : Set ThetaWNoteD) (a : ThetaWNoteD), a ∈ H X ↔ Ehull k a ⊆ H X

/-- The operator `H[Z]` of Freund, Definition 5.4: `H[Z](X) = H(Z ∪ X)`. -/
def adjoin (H : Set ThetaWNoteD → Set ThetaWNoteD) (Z : Set ThetaWNoteD) :
    Set ThetaWNoteD → Set ThetaWNoteD :=
  fun X => H (Z ∪ X)

theorem adjoin_apply (H : Set ThetaWNoteD → Set ThetaWNoteD) (Z X : Set ThetaWNoteD) :
    adjoin H Z X = H (Z ∪ X) := rfl

theorem IsOperator.subset {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : IsOperator H)
    (X : Set ThetaWNoteD) : X ⊆ H X :=
  hH.1 X

/-- Exercise 5.5 (b): an operator is monotone. -/
theorem IsOperator.mono {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : IsOperator H)
    {X Y : Set ThetaWNoteD} (h : X ⊆ Y) : H X ⊆ H Y :=
  hH.2 X Y (h.trans (hH.1 Y))

theorem IsOperator.idem {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : IsOperator H)
    (X : Set ThetaWNoteD) : H (H X) = H X :=
  le_antisymm (hH.2 _ _ le_rfl) (hH.1 _)

theorem Nice.isOperator {k : ℕ} {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : Nice k H) :
    IsOperator H := hH.1

theorem Nice.mem_iff {k : ℕ} {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : Nice k H)
    {X : Set ThetaWNoteD} {a : ThetaWNoteD} : a ∈ H X ↔ Ehull k a ⊆ H X :=
  hH.2 X a

/-- Exercise 5.5 (a): `H_{k,α}` is an operator. -/
theorem Hop_isOperator (k : ℕ) (a : ThetaWNoteD) : IsOperator (Hop k a) :=
  ⟨fun _ _ hx _ _ _ hX => hX hx,
    fun _ _ hXY _ hx c d hac hY => hx c d hac fun _ hy => hXY hy c d hac hY⟩

/-- Exercise 5.5 (a): `H_{k,α}` is a nice operator at level `k` (by Proposition 3.9). -/
theorem Hop_nice (k : ℕ) (a : ThetaWNoteD) : Nice k (Hop k a) :=
  ⟨Hop_isOperator k a, fun _ _ =>
    ⟨fun hx _ hg c d hac hX => mem_Cset_iff_Ehull_subset.mp (hx c d hac hX) hg,
      fun h c d hac hX => mem_Cset_iff_Ehull_subset.mpr fun _ hg => h hg c d hac hX⟩⟩

theorem Hop_mono {k : ℕ} {a : ThetaWNoteD} {X Y : Set ThetaWNoteD} (h : X ⊆ Y) :
    Hop k a X ⊆ Hop k a Y :=
  (Hop_isOperator k a).mono h

/-- Exercise 5.5 (c): `H[Z]` is an operator when `H` is. -/
theorem IsOperator.adjoin {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : IsOperator H)
    (Z : Set ThetaWNoteD) : IsOperator (adjoin H Z) :=
  ⟨fun _ => Set.subset_union_right.trans (hH.1 _),
    fun _ _ h => hH.2 _ _ (Set.union_subset (Set.subset_union_left.trans (hH.1 _)) h)⟩

/-- Exercise 5.5 (c): `H[Z]` is nice when `H` is. -/
theorem Nice.adjoin {k : ℕ} {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : Nice k H)
    (Z : Set ThetaWNoteD) : Nice k (adjoin H Z) :=
  ⟨hH.1.adjoin Z, fun X a => hH.2 (Z ∪ X) a⟩

/-- Exercise 5.5 (c): `H[Z] = H` when `Z ⊆ H(∅)`. -/
theorem adjoin_eq_self {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : IsOperator H)
    {Z : Set ThetaWNoteD} (hZ : Z ⊆ H ∅) : adjoin H Z = H := by
  funext X
  exact le_antisymm
    (hH.2 _ _ (Set.union_subset (hZ.trans (hH.mono (Set.empty_subset X))) (hH.1 X)))
    (hH.mono Set.subset_union_right)

/-- Exercise 5.5 (c): `H[Z][Z'] = H[Z ∪ Z']`. -/
theorem adjoin_adjoin (H : Set ThetaWNoteD → Set ThetaWNoteD) (Z Z' : Set ThetaWNoteD) :
    adjoin (adjoin H Z) Z' = adjoin H (Z ∪ Z') := by
  funext X
  simp only [adjoin, Set.union_assoc]

/- **Not generalized**: Freund's Exercise 5.5 (d), the
converse characterization of niceness ("`H` is nice at level `k` iff every `H(X)` contains
every `Ω_j` and contains a sum exactly when it contains every summand"), needs an *extra*
clause for a collapse `ϑ_j` with `j > k`, since `E_k` there is *transparent*
(`E_k(ϑ_j ξ) = E_k(ξ)`, `ThetaW/Basic.E_theta_of_lt`) rather than terminating at a single
`ϑ_j`-clause as in the one-level file (where the only collapsing function *is* the hull's own
level).  The extra clause needed is genuinely new content (an `H(ϑ_j ξ) ↔ H(ξ)` transparency
axiom for `j > k`), not a restatement of the sum/`Ω` clauses already available, and it is not
needed by anything else in this file (`Hop_nice` above is proved directly from
`mem_Cset_iff_Ehull_subset`, not from this characterization) — so it is left unported. -/

section Nice

variable {k : ℕ} {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : Nice k H) {X : Set ThetaWNoteD}
include hH

theorem Nice.Omega_mem (j : ℕ) : Omega j ∈ H X := hH.mem_iff.mpr (by simp)

theorem Nice.zero_mem : zero ∈ H X := hH.mem_iff.mpr (by simp)

theorem Nice.one_mem : one ∈ H X := hH.mem_iff.mpr (by simp)

theorem Nice.ofNat_mem (n : ℕ) : ofNat n ∈ H X := hH.mem_iff.mpr (by simp)

/-- Exercise 5.5 (e): `α, β ∈ H(X)` give `α + β ∈ H(X)`. -/
theorem Nice.add_mem {a b : ThetaWNoteD} (ha : a ∈ H X) (hb : b ∈ H X) : a + b ∈ H X :=
  hH.mem_iff.mpr ((Ehull_add_subset_hull k a b).trans
    (Set.union_subset (hH.mem_iff.mp ha) (hH.mem_iff.mp hb)))

theorem Nice.nadd_mem {a b : ThetaWNoteD} (ha : a ∈ H X) (hb : b ∈ H X) : nadd a b ∈ H X :=
  hH.mem_iff.mpr ((Ehull_nadd_subset_hull k a b).trans
    (Set.union_subset (hH.mem_iff.mp ha) (hH.mem_iff.mp hb)))

/-- Exercise 5.5 (e): `α ∈ H(X)` gives `ω · α ∈ H(X)`. -/
theorem Nice.omegaMul_mem {a : ThetaWNoteD} (ha : a ∈ H X) : omegaMul a ∈ H X :=
  hH.mem_iff.mpr ((Ehull_omegaMul_subset_hull k a).trans (hH.mem_iff.mp ha))

/-- Exercise 5.5 (e): `α ∈ H(X)` gives `ω(α) = ω^α ∈ H(X)`. -/
theorem Nice.omegaPow_mem {a : ThetaWNoteD} (ha : a ∈ H X) : omegaPow a ∈ H X :=
  hH.mem_iff.mpr ((Ehull_omegaPow_hull k a).symm ▸ hH.mem_iff.mp ha)

theorem Nice.succ_mem {a : ThetaWNoteD} (ha : a ∈ H X) : succ a ∈ H X :=
  hH.mem_iff.mpr ((Ehull_succ_subset_hull k a).trans (hH.mem_iff.mp ha))

end Nice

/-! ### The facts used by a Theorem-6.7-style collapsing argument, level `k` -/

/-- `α ≺ α + ω(β)`. -/
theorem lt_add_omegaPow_hull (a b : ThetaWNoteD) : a < a + omegaPow b := by
  have h := add_lt_add_left a (lt_of_lt_of_le zero_lt_one (one_le_omegaPow b))
  rwa [add_zero] at h

/-- `α + ω(β') + ω(β') ≺ α + ω(β)` for `β' ≺ β`. -/
theorem add_omegaPow_add_omegaPow_lt_hull (a : ThetaWNoteD) {b b' : ThetaWNoteD} (h : b' < b) :
    a + omegaPow b' + omegaPow b' < a + omegaPow b := by
  rw [add_assoc]
  exact add_lt_add_left a (add_lt_omegaPow (omegaPow_lt_omegaPow h) (omegaPow_lt_omegaPow h))

/-- `η = α + ω(β) ≺ Ω_k` whenever `α, β ≺ Ω_k`: the domain-safety bound needed for `ϑ_k η`
(mirrors `ThetaW/Veblen.dom_phi_of_lt`). -/
theorem add_omegaPow_lt_Omega {k : ℕ} {a b : ThetaWNoteD} (ha : a < Omega k) (hb : b < Omega k) :
    a + omegaPow b < Omega k :=
  add_lt_Omega ha (omegaPow_lt_Omega hb)

/-- `ϑ_k` is domain-safe at `η = α + ω(β)` whenever `α, β ≺ Ω_k` (mirrors
`ThetaW/Veblen.dom_phi_of_lt`, which is exactly this fact for `η = Ω_{k+1}·ρ + β`; here `η`
has no `Ω_{k+1}·ρ` summand, only the plain `+`; `G_k` vanishes on any normal term below
`Ω_k` directly, `ThetaW/Veblen.G_eq_nil_of_lt_Omega`, so no separate additive decomposition of
`G_k` is even needed). -/
theorem dom_theta_add_omegaPow_of_lt {k : ℕ} {a b : ThetaWNoteD} (ha : a < Omega k)
    (hb : b < Omega k) : Dom (ThetaWTerm.theta k (a + omegaPow b).1) :=
  ThetaWTerm.dom_theta_of_G_nil (a + omegaPow b).2.2
    (ThetaWTerm.G_eq_nil_of_lt_Omega (a + omegaPow b).2.1 (add_omegaPow_lt_Omega ha hb))

/-- Theorem 6.7: from `α, β ∈ H_{k,α}(X)`, `α, β ≺ Ω_k`, we get `η = α + ω(β) ∈ H_{k,η}(X)`
(Exercise 5.5 and Proposition 3.11 (a)). -/
theorem add_omegaPow_mem_Hop {k : ℕ} {a b : ThetaWNoteD} {X : Set ThetaWNoteD}
    (ha : a ∈ Hop k a X) (hb : b ∈ Hop k a X) :
    a + omegaPow b ∈ Hop k (a + omegaPow b) X :=
  Hop_subset_Hop (lt_add_omegaPow_hull a b) X
    ((Hop_nice k a).add_mem ha ((Hop_nice k a).omegaPow_mem hb))

/-- Theorem 6.7: from `α, β ∈ H_{k,α}(X)`, `α, β ≺ Ω_k`, we get `ϑ_k η ∈ H_{k,η}(X)` for
`η = α + ω(β)` (Proposition 3.11 (b), with the domain side condition from
`dom_theta_add_omegaPow_of_lt`). -/
theorem theta_add_omegaPow_mem_Hop {k : ℕ} {a b : ThetaWNoteD} {X : Set ThetaWNoteD}
    (ha : a ∈ Hop k a X) (hb : b ∈ Hop k a X) (haΩ : a < Omega k) (hbΩ : b < Omega k) :
    thetaD k (a + omegaPow b) (dom_theta_add_omegaPow_of_lt haΩ hbΩ) ∈
      Hop k (a + omegaPow b) X :=
  theta_mem_Hop (add_omegaPow_mem_Hop ha hb) le_rfl (dom_theta_add_omegaPow_of_lt haΩ hbΩ)

end ThetaWNoteD

end OrdinalAnalysis
