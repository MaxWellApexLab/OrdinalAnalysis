/-
  The notation interface for the ID_n station: `CollapsingNotation` and `CollapsingLevel`.

  Source: `idn_abstraction_plan.md` §2, compiled first as a scratch
  file (`Iface_final.lean`) against master ff1ce1a.  Landed here unchanged in substance.

  Layer 0: the generic operator algebra (`IsOperator`, `adjoin`, `Nice`), over any `O : Type`,
  with no notation content at all — this is `Ordinal/Theta/Hull.lean`'s
  `ThetaNote.IsOperator/adjoin/Nice` (l. 368–428) with `Ehull` abstracted to a support function
  `supp`.

  Layer 1: `class CollapsingNotation`, a mixin over `OrdinalNotation` (Cantor arithmetic beyond
  what `OrdinalNotation` already gives, the principal terms, the support function `supp`, and the
  Buchholz operators `H_α`).  The operator layer (`Hop`, `Nice supp`) lives here, **not** in
  `CollapsingLevel`: Buchholz 1992 Definition 4.2 has one hull `C(α, β)`, closed under every
  `ϑ_j` restricted to domain arguments below `α`, with `C_κ(α) := C(α, κ)` recovering the
  per-level hulls; there is one operator family for the whole notation system, not one per level.
  This resolves the R1 risk of the plan (§2b (ii), §5.3) in favour of the level-free reading, which
  is what the scratch file already compiled against.

  Layer 2: `structure CollapsingLevel`, one level `k`: the regular cardinal `Ω := Ω_{k+1}`, the
  domain `D` of `ϑ_k`, `ϑ_k` itself (total, with a junk value outside `D`), and the hull
  hypothesis `HullHyp` of the collapsing theorem at this level, together with the fields that
  ID₁'s `Collapsing`, `Elimination` (Cor 7.2) and `LowerBound` consume (Freund, Propositions 3.9
  and 3.11, per level with `κ` as a parameter).  `HullHyp` is level data (it quantifies over `D`
  and `theta`, which are level fields), so it stays here even though it is stated in terms of the
  level-free `CollapsingNotation.Hop`.

  Derived facts (`Hull.lean` l. 504–603) are proved once, generically, at the end.
-/
import OrdinalAnalysis.Ordinal.Notation

set_option autoImplicit false

namespace OrdinalAnalysis
namespace Notn

/-! ## Layer 0: operators, generically (no notation content) -/

section Op
variable {O : Type}

/-- An operator on subsets of `O`: inflationary and monotone in the sense that if `X` is already
inside the closure of `Y`, closing `X` adds nothing beyond the closure of `Y`. -/
def IsOperator (H : Set O → Set O) : Prop :=
  (∀ X, X ⊆ H X) ∧ ∀ X Y, X ⊆ H Y → H X ⊆ H Y

/-- `H[Z](X) := H(Z ∪ X)`. -/
def adjoin (H : Set O → Set O) (Z : Set O) : Set O → Set O := fun X => H (Z ∪ X)

/-- Nice relative to a support function (`supp = Ehull` for `ϑ`). -/
def Nice (supp : O → Set O) (H : Set O → Set O) : Prop :=
  IsOperator H ∧ ∀ (X : Set O) (a : O), a ∈ H X ↔ supp a ⊆ H X

theorem IsOperator.mono {H : Set O → Set O} (hH : IsOperator H) {X Y : Set O} (h : X ⊆ Y) :
    H X ⊆ H Y := hH.2 X Y (h.trans (hH.1 Y))

theorem IsOperator.adjoin {H : Set O → Set O} (hH : IsOperator H) (Z : Set O) :
    IsOperator (adjoin H Z) :=
  ⟨fun _ => Set.subset_union_right.trans (hH.1 _),
    fun _ _ h => hH.2 _ _ (Set.union_subset (Set.subset_union_left.trans (hH.1 _)) h)⟩

theorem adjoin_adjoin (H : Set O → Set O) (Z Z' : Set O) :
    adjoin (adjoin H Z) Z' = adjoin H (Z ∪ Z') := by
  funext X; simp only [adjoin, Set.union_assoc]

end Op

/-! ## Layer 1: the global collapsing notation -/

/-- Cantor arithmetic beyond `OrdinalNotation`, a support function, and the operators `H_α`.
A mixin, as `OrdinalNotation` is. -/
class CollapsingNotation (O : Type) [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O] where
  zero : O
  zero_le : ∀ a : O, zero ≤ a
  add : O → O → O
  add_zero : ∀ a, add a zero = a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_lt_add_left : ∀ (a : O) {b c : O}, b < c → add a b < add a c
  le_add_left : ∀ a b : O, b ≤ add a b
  add_lt_omegaPow : ∀ {a x y : O}, x < OrdinalNotation.omegaPow a →
    y < OrdinalNotation.omegaPow a → add x y < OrdinalNotation.omegaPow a
  zero_lt_one : zero < OrdinalNotation.one
  omegaMul : O → O
  omegaMul_lt_omegaMul : ∀ {a b : O}, a < b → omegaMul a < omegaMul b
  /-- principal = ε-number-like (Ω's and ϑ-values) -/
  IsPrin : O → Prop
  omegaMul_prin : ∀ {p : O}, IsPrin p → omegaMul p = p
  omegaMul_lt_prin : ∀ {x p : O}, IsPrin p → x < p → omegaMul x < p
  nadd_lt_prin : ∀ {x y p : O}, IsPrin p → x < p → y < p → OrdinalNotation.nadd x y < p
  one_lt_prin : ∀ {p : O}, IsPrin p → OrdinalNotation.one < p
  ofNat_lt_prin : ∀ {p : O}, IsPrin p → ∀ n, OrdinalNotation.ofNat n < p
  /-- `E(α)` over all levels -/
  supp : O → Set O
  supp_add : ∀ a b, supp (add a b) ⊆ supp a ∪ supp b
  supp_nadd : ∀ a b, supp (OrdinalNotation.nadd a b) ⊆ supp a ∪ supp b
  supp_omegaPow : ∀ a, supp (OrdinalNotation.omegaPow a) = supp a
  supp_omegaMul : ∀ a, supp (omegaMul a) ⊆ supp a
  supp_zero : supp zero = ∅
  supp_one : supp OrdinalNotation.one = ∅
  supp_ofNat : ∀ n, supp (OrdinalNotation.ofNat n) = ∅
  /-- `H_α` -/
  Hop : O → Set O → Set O
  Hop_nice : ∀ a, Nice supp (Hop a)
  Hop_subset_Hop : ∀ {a b : O}, a < b → ∀ X, Hop a X ⊆ Hop b X

/-! ## Layer 2: one collapsing level -/

/-- One level `k` of a collapsing notation: the regular `Ω := Ω_{k+1}`, the domain `D` of
`ϑ_k`, the function `ϑ_k` itself (total; a junk value outside `D`), and the hypothesis
`HullHyp a X` of the collapsing theorem at this level.  Only the facts the ID₁ calculus
files use (Collapsing, Elimination, LowerBound) are fields. -/
structure CollapsingLevel (O : Type) [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
    [CollapsingNotation O] where
  Omega : O
  isPrin_Omega : CollapsingNotation.IsPrin Omega
  supp_Omega : CollapsingNotation.supp Omega = ∅
  D : O → Prop
  theta : O → O
  isPrin_theta : ∀ {a}, D a → CollapsingNotation.IsPrin (theta a)
  theta_lt_Omega : ∀ a, theta a < Omega
  HullHyp : O → Set O → Prop
  hullHyp_mono : ∀ {a b X}, HullHyp a X → a ≤ b → HullHyp b X
  /-- Prop 3.9 via 3.10: `δ ∈ H_α(X) ∩ Ω` is below `ϑ ξ` for `α ≺ ξ ∈ D`. -/
  hullHyp_lt_theta : ∀ {a c d X}, HullHyp a X → a < c → D c →
    d ∈ CollapsingNotation.Hop a X → d < Omega → d < theta c
  hullHyp_union_singleton : ∀ {a d g X}, HullHyp a X → d ∈ CollapsingNotation.Hop a X →
    d < Omega → g < d → HullHyp a (X ∪ {g})
  /-- Prop 3.11 (b), restricted to the domain. -/
  theta_mem_Hop : ∀ {a b X}, a ∈ CollapsingNotation.Hop b X → a ≤ b → D a →
    theta a ∈ CollapsingNotation.Hop b X
  /-- Prop 3.11 (c), restricted to the domain. -/
  theta_lt_theta_of_mem_Hop : ∀ {a b c X}, HullHyp a X → a ≤ b → b < c →
    b ∈ CollapsingNotation.Hop a X → D b → D c → theta b < theta c
  /-- **The Dom side condition**: the heights `η = α + ω^β` of the collapsing theorem are in
  the domain.  ID₁: `D = True`.  ThetaW: `G_k(η) ⊆ G_k(α) ∪ G_k(β)`, and every element of `G_k` of
  a member of `H_α(X)` (with `HullHyp α X`) is `≺ α ≤ η`. -/
  dom_add_omegaPow : ∀ {a b X}, HullHyp a X → a ∈ CollapsingNotation.Hop a X →
    b ∈ CollapsingNotation.Hop a X →
    D (CollapsingNotation.add a (OrdinalNotation.omegaPow b))

namespace CollapsingLevel

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
  [CollapsingNotation O] (L : CollapsingLevel O)

open CollapsingNotation OrdinalNotation

/-- The stage indices `α ⪯ Ω` of this level (ID₁'s `Stage` at `L = thetaLevel`). -/
abbrev Stage : Type := {a : O // a ≤ L.Omega}

/-! Derived facts, proved ONCE (ID₁ `Hull.lean` l. 509–603, generic). -/

theorem Nice.add_mem {H : Set O → Set O} (hH : Nice supp H) {X : Set O} {a b : O}
    (ha : a ∈ H X) (hb : b ∈ H X) : add a b ∈ H X :=
  (hH.2 X _).mpr ((supp_add a b).trans
    (Set.union_subset ((hH.2 X a).mp ha) ((hH.2 X b).mp hb)))

theorem Nice.omegaPow_mem {H : Set O → Set O} (hH : Nice supp H) {X : Set O} {a : O}
    (ha : a ∈ H X) : omegaPow a ∈ H X :=
  (hH.2 X _).mpr ((supp_omegaPow a).symm ▸ (hH.2 X a).mp ha)

theorem Omega_mem {H : Set O → Set O} (hH : Nice supp H) {X : Set O} : L.Omega ∈ H X :=
  (hH.2 X _).mpr (by rw [L.supp_Omega]; exact Set.empty_subset _)

theorem lt_add_omegaPow (a b : O) : a < add a (omegaPow b) := by
  have h := add_lt_add_left a (lt_of_lt_of_le zero_lt_one (OrdinalNotation.one_le_omegaPow b))
  rwa [CollapsingNotation.add_zero] at h

theorem add_omegaPow_add_omegaPow_lt (a : O) {b b' : O} (h : b' < b) :
    add (add a (omegaPow b')) (omegaPow b') < add a (omegaPow b) := by
  rw [CollapsingNotation.add_assoc]
  exact add_lt_add_left a (add_lt_omegaPow (omegaPow_lt_omegaPow h) (omegaPow_lt_omegaPow h))

theorem add_omegaPow_mem_Hop {a b : O} {X : Set O} (ha : a ∈ Hop a X) (hb : b ∈ Hop a X) :
    add a (omegaPow b) ∈ Hop (add a (omegaPow b)) X :=
  Hop_subset_Hop (lt_add_omegaPow a b) X
    (Nice.add_mem (Hop_nice a) ha (Nice.omegaPow_mem (Hop_nice a) hb))

/-- ID₁ `theta_add_omegaPow_mem_Hop`, now with the domain side condition discharged by the
field `dom_add_omegaPow` (hence the extra `HullHyp` hypothesis, which every ID₁ call site has). -/
theorem theta_add_omegaPow_mem_Hop {a b : O} {X : Set O} (hX : L.HullHyp a X)
    (ha : a ∈ Hop a X) (hb : b ∈ Hop a X) :
    L.theta (add a (omegaPow b)) ∈ Hop (add a (omegaPow b)) X :=
  L.theta_mem_Hop (add_omegaPow_mem_Hop ha hb) le_rfl (L.dom_add_omegaPow hX ha hb)

/-- The ϑ-comparison used twice in the (Fix)/cut cases of Theorem 6.7. -/
theorem theta_lt_theta_add {a b b' : O} {X : Set O} (hX : L.HullHyp a X)
    (ha : a ∈ Hop a X) (hb : b ∈ Hop a X) (hb' : b' ∈ Hop a X) (h : b' < b) :
    L.theta (add a (omegaPow b')) < L.theta (add a (omegaPow b)) :=
  L.theta_lt_theta_of_mem_Hop hX (le_of_lt (lt_add_omegaPow a b'))
    (add_lt_add_left a (omegaPow_lt_omegaPow h))
    (Nice.add_mem (Hop_nice a) ha (Nice.omegaPow_mem (Hop_nice a) hb'))
    (L.dom_add_omegaPow hX ha hb') (L.dom_add_omegaPow hX ha hb)

end CollapsingLevel

/-! ## Layer 3 (sketch, C4 only): the tower of levels

Not consumed by anything in this file or by `ThetaInstance.lean`; kept only because the bare
structure (no instance) compiles with no `sorry`.  Buchholz's Theorem 4.8 moves along these
cross-level facts (`κ := π`, `μ' ≺ μ`).  Not an ID₁ concept — `ThetaNote` has a single level, so
there is no `CollapsingTower ThetaNote` instance; `ThetaWNoteD`'s instance is N1/C4 work and is
not attempted here (it needs the hull fields of `ThetaWHullFacts`, `ThetaWInstance.lean`, plus two
more facts that are not yet proved anywhere). -/
structure CollapsingTower (O : Type) [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
    [CollapsingNotation O] where
  lev : ℕ → CollapsingLevel O
  Omega_strictMono : StrictMono fun k => (lev k).Omega
  Omega_lt_theta_succ : ∀ k a, (lev (k + 1)).D a → (lev k).Omega < (lev (k + 1)).theta a
  /-- `𝒜(Θ; γ, κ, μ)` quantifies over all `τ ⪰ κ`: the hypothesis passes upwards. -/
  hullHyp_up : ∀ {k j a X}, (lev k).HullHyp a X → k ≤ j → (lev j).HullHyp a X
  /-- `ω · Ω_{k+1} = Ω_{k+1}`, `Ω_k + Ω_{k+1} = Ω_{k+1}` (the rank `Ω_k + ω·α` of `I_k^{≺α}`). -/
  add_Omega_Omega :
    ∀ k, CollapsingNotation.add (lev k).Omega (lev (k + 1)).Omega = (lev (k + 1)).Omega

end Notn
end OrdinalAnalysis
