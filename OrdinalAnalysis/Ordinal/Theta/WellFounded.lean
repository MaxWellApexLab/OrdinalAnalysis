/-
  The ϑ-order on normal terms is well founded.

  Source: T. Arai, *Lectures on ordinal analysis*, arXiv:2304.00246, §1.6 (Definition 1.27,
  Lemma 1.29, Lemma 1.33), where the argument is given for Buchholz's `ψ` inside `ID₁`,
  following the distinguished classes of Buchholz.  Here it is carried out for the ϑ-notation of Freund, arXiv:2204.09321,
  Definition 3.1, in the metatheory, where the accessible part `Acc` is available for all
  predicates at once.

  Write `W` for the accessible part of `≺` on normal terms.

  * (Arai, Definition 1.27.)  The distinguished class is `M = {α | E(α) ⊆ W}`: the terms all
    of whose ϑ-subterms at top level are accessible.  (Arai's `SC(α) ∩ Ω` becomes `E(α)`.)
  * (Sums.)  If every exponent of a normal sum lies in a class `S` closed under taking and
    forming sums, and is accessible for `≺` restricted to `S`, then so is the sum.  This is
    the usual double induction for the lexicographic order on non-increasing lists: on the
    first exponent, and for a fixed first exponent on the rest of the sum.
  * (Arai, Lemma 1.29, the inclusion `M ∩ Ω ⊆ W`.)  A term below `Ω` all of whose ϑ-subterms
    at top level are accessible is accessible, by induction on the length.
  * (`≺` restricted to `M` is well founded.)  Below `Ω` this is the previous item; `Ω` is
    accessible in `M` because everything in `M` below `Ω` is in `W`; a term above `Ω` is a sum
    whose exponents are shorter terms of `M`.  In Arai's setting this step needs the Gentzen
    jump (Lemmas 1.31 and 1.32) to reach each `ω_n(Ω + 1)`; in the metatheory an induction on
    the length of terms replaces it, since the exponents of a normal sum are subterms.
  * (Arai, Lemma 1.33, for ϑ.)  If `α ∈ M` and `ϑ ξ ∈ W` for all `ξ ∈ M` with `ξ ≺ α`, then
    `ϑ α ∈ W`.  Every `γ ≺ ϑ α` is shown to lie in `W` by induction on the length of `γ`.  A
    sum below `ϑ α` has its exponents below `ϑ α`.  For `γ = ϑ ξ`, Definition 3.1 (ii') of
    Freund leaves two cases: either `ξ ≺ α` and `E(ξ) ≺* ϑ α`, and then the elements of
    `E(ξ)` are shorter than `γ`, hence in `W`, so `ξ ∈ M` and `ϑ ξ ∈ W` by hypothesis; or
    `ϑ ξ ≼ δ` for some `δ ∈ E(α) ⊆ W`, and `W` is downward closed.
  * By induction along `≺` restricted to `M`, `ϑ α ∈ W` for every `α ∈ M`.  Then every term
    below `Ω` is in `W` (induction on the length: for `ϑ ξ` the elements of `E(ξ)` are shorter
    and below `Ω`, so `ξ ∈ M`), hence `Ω ∈ W`, and every term above `Ω` is a sum of shorter
    terms, hence in `W`.
-/
import OrdinalAnalysis.Ordinal.Theta.Instance
import Mathlib.SetTheory.Ordinal.Basic

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaTerm

/-! ### Accessibility on normal terms -/

/-- The order `≺` on normal terms, restricted to a class `S`: `RelOn S a b` holds iff `a` is
normal, `a ∈ S`, and `a ≺ b`. -/
def RelOn (S : ThetaTerm → Prop) (a b : ThetaTerm) : Prop := NF a ∧ S a ∧ a < b

/-- The order `≺` on normal terms. -/
abbrev Rel : ThetaTerm → ThetaTerm → Prop := RelOn fun _ => True

/-- `a` lies in the accessible part `W` of `≺` on normal terms. -/
def IsAcc (a : ThetaTerm) : Prop := Acc Rel a

/-- The distinguished class `M` (Arai, Definition 1.27): all ϑ-subterms at top level, i.e.
the elements of `E(α)`, are accessible. -/
def Dist (a : ThetaTerm) : Prop := ∀ g ∈ E a, IsAcc g

/-- `W` is downward closed along `≼` on normal terms. -/
theorem IsAcc.of_le {a b : ThetaTerm} (hb : IsAcc b) (ha : NF a) (h : a ≤ b) : IsAcc a := by
  rcases h with h | rfl
  · exact Acc.inv hb ⟨ha, trivial, h⟩
  · exact hb

/-- An accessible term is accessible for the order restricted to any class. -/
theorem IsAcc.relOn {a : ThetaTerm} (h : IsAcc a) (S : ThetaTerm → Prop) :
    Acc (RelOn S) a :=
  Subrelation.accessible (fun ⟨h1, _, h3⟩ => ⟨h1, trivial, h3⟩) h

/-- `0 = ⟨⟩` has no predecessors. -/
theorem acc_nil (S : ThetaTerm → Prop) : Acc (RelOn S) (sum []) :=
  Acc.intro _ fun _ h => absurd h.2.2 (not_lt_nil _)

theorem mem_E_ofList {g : ThetaTerm} {xs : List ThetaTerm} :
    g ∈ E (ofList xs) ↔ ∃ x ∈ xs, g ∈ E x := by
  match xs with
  | [] => simp
  | [x] =>
    by_cases h : IsPrin x
    · rw [ofList_singleton_prin h]; simp
    · rw [ofList_singleton_not_prin h]; exact mem_E_sum
  | _ :: _ :: _ => exact mem_E_sum

theorem lt_Omega_of_mem_E {a g : ThetaTerm} (hg : g ∈ E a) : g < Omega := by
  obtain ⟨d, rfl⟩ := exists_eq_theta_of_mem_E hg
  exact theta_lt_Omega d

theorem CNF.tail {x : ThetaTerm} {xs : List ThetaTerm} (h : CNF (x :: xs)) : CNF xs :=
  ⟨fun e he => h.1 e (List.mem_cons_of_mem x he), h.2.of_cons⟩

theorem CNF.le_head {x : ThetaTerm} {xs : List ThetaTerm} (h : CNF (x :: xs)) :
    ∀ e ∈ x :: xs, e ≤ x := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact le_refl' _
  · exact SortedDesc.le_head h.2 he

/-! ### Sums of accessible exponents are accessible -/

section Sums

variable (S : ThetaTerm → Prop) (hS : ∀ xs, S (ofList xs) ↔ ∀ x ∈ xs, S x)
include hS

/-- The inner induction: for a fixed first exponent `x`, assuming the claim for all smaller
first exponents, `ofList (x :: ys)` is accessible whenever `ofList ys` is. -/
theorem acc_ofList_cons_aux {x : ThetaTerm}
    (ih : ∀ x', RelOn S x' x → ∀ ys, CNF ys → (∀ y ∈ ys, S y) → (∀ y ∈ ys, y ≤ x') →
      Acc (RelOn S) (ofList ys)) :
    ∀ t, Acc (RelOn S) t → ∀ ys, ofList ys = t → Acc (RelOn S) (ofList (x :: ys)) := by
  intro t ht
  induction ht with
  | intro t _ ihA =>
  intro ys hys
  subst hys
  refine Acc.intro _ fun z ⟨hz, hSz, hlt⟩ => ?_
  have hzeq : ofList (toList z) = z := ofList_toList hz
  have hzl : CNF (toList z) := NF.cnf_toList hz
  have hSl : ∀ e ∈ toList z, S e := (hS (toList z)).mp (by rw [hzeq]; exact hSz)
  rw [← hzeq] at hlt ⊢
  rw [ofList_lt_ofList] at hlt
  generalize toList z = zs at hlt hzl hSl
  cases zs with
  | nil => exact acc_nil S
  | cons z0 zs =>
    rcases (cons_lt_cons_iff _ _ _ _).mp hlt with h | ⟨rfl, h⟩
    · exact ih z0 ⟨hzl.1 z0 List.mem_cons_self, hSl z0 List.mem_cons_self, h⟩ (z0 :: zs) hzl
        hSl hzl.le_head
    · refine ihA (ofList zs) ⟨nf_ofList_iff.mpr hzl.tail,
        (hS zs).mpr (fun e he => hSl e (List.mem_cons_of_mem _ he)),
        ofList_lt_ofList.mpr h⟩ zs rfl

/-- The outer induction, on the first exponent: if `x` is accessible for `≺` restricted to
`S`, so is every normal sum of exponents `≼ x` in `S`. -/
theorem acc_ofList_of_le (x : ThetaTerm) (hx : Acc (RelOn S) x) :
    ∀ ys, CNF ys → (∀ y ∈ ys, S y) → (∀ y ∈ ys, y ≤ x) → Acc (RelOn S) (ofList ys) := by
  induction hx with
  | intro x _ ihx =>
  intro ys
  induction ys with
  | nil => intro _ _ _; exact acc_nil S
  | cons y ys ihys =>
    intro hc hSy hle
    have ht : Acc (RelOn S) (ofList ys) :=
      ihys hc.tail (fun e he => hSy e (List.mem_cons_of_mem _ he))
        (fun e he => hle e (List.mem_cons_of_mem _ he))
    rcases hle y List.mem_cons_self with hlt | rfl
    · exact ihx y ⟨hc.1 y List.mem_cons_self, hSy y List.mem_cons_self, hlt⟩ (y :: ys) hc hSy
        hc.le_head
    · exact acc_ofList_cons_aux S hS ihx _ ht ys rfl

/-- A normal sum of exponents in `S` that are accessible for `≺` restricted to `S` is
accessible for `≺` restricted to `S`. -/
theorem acc_ofList (ys : List ThetaTerm) (hc : CNF ys) (hSy : ∀ y ∈ ys, S y)
    (hA : ∀ y ∈ ys, Acc (RelOn S) y) : Acc (RelOn S) (ofList ys) := by
  cases ys with
  | nil => exact acc_nil S
  | cons y ys => exact acc_ofList_of_le S hS y (hA y List.mem_cons_self) _ hc hSy hc.le_head

/-- The same for a normal term and its list of exponents. -/
theorem acc_of_toList {t : ThetaTerm} (ht : NF t) (hSy : ∀ y ∈ toList t, S y)
    (hA : ∀ y ∈ toList t, Acc (RelOn S) y) : Acc (RelOn S) t := by
  have := acc_ofList S hS (toList t) (NF.cnf_toList ht) hSy hA
  rwa [ofList_toList ht] at this

end Sums

/-- A normal term whose exponents are accessible is accessible. -/
theorem isAcc_of_toList {t : ThetaTerm} (ht : NF t) (hA : ∀ y ∈ toList t, IsAcc y) :
    IsAcc t :=
  acc_of_toList (fun _ => True) (fun _ => by simp) ht (fun _ _ => trivial) hA

theorem dist_ofList_iff (xs : List ThetaTerm) : Dist (ofList xs) ↔ ∀ x ∈ xs, Dist x := by
  constructor
  · intro h x hx g hg
    exact h g (mem_E_ofList.mpr ⟨x, hx, hg⟩)
  · intro h g hg
    obtain ⟨x, hx, hg⟩ := mem_E_ofList.mp hg
    exact h x hx g hg

theorem Dist.of_mem {x : ThetaTerm} {xs : List ThetaTerm} (h : Dist (sum xs)) (hx : x ∈ xs) :
    Dist x :=
  fun g hg => h g (mem_E_of_mem hx hg)

/-! ### The distinguished class below `Ω` (Arai, Lemma 1.29) -/

/-- Arai, Lemma 1.29 (the inclusion `M ∩ Ω ⊆ W`): a normal term below `Ω` whose elements of
`E` are accessible is accessible. -/
theorem isAcc_of_dist_of_lt_Omega : ∀ {a : ThetaTerm}, NF a → Dist a → a < Omega → IsAcc a
  | Omega, _, _, h => absurd h not_Omega_lt_Omega
  | theta ξ, _, hM, _ => hM (theta ξ) (by simp)
  | sum xs, ha, hM, hlt => by
    have hxs : ∀ x ∈ xs, x < Omega := (sum_lt_prin_iff isPrin_Omega ha.desc).mp hlt
    exact isAcc_of_toList ha fun x hx =>
      isAcc_of_dist_of_lt_Omega (ha.of_mem hx) (hM.of_mem hx) (hxs x hx)
termination_by a => l a
decreasing_by exact l_lt_of_mem hx

/-- Conversely, the elements of `E(α)` of an accessible normal term are accessible, since they
are `≼ α`. -/
theorem IsAcc.dist {a : ThetaTerm} (h : IsAcc a) (ha : NF a) : Dist a :=
  fun _ hg => h.of_le (NF.of_mem_E ha hg) (le_of_mem_E ha hg)

/-! ### The order restricted to the distinguished class is well founded -/

/-- Every normal term of the distinguished class is accessible for `≺` restricted to the
distinguished class. -/
theorem acc_dist : ∀ (n : ℕ) {a : ThetaTerm}, l a ≤ n → NF a → Dist a → Acc (RelOn Dist) a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a hn ha hM
  rcases lt_trichotomy' a Omega with h | rfl | h
  · exact (isAcc_of_dist_of_lt_Omega ha hM h).relOn Dist
  · exact Acc.intro _ fun z ⟨hz, hMz, hlt⟩ =>
      (isAcc_of_dist_of_lt_Omega hz hMz hlt).relOn Dist
  · obtain ⟨c, cs, rfl, _⟩ := Omega_lt_iff.mp h
    refine acc_of_toList Dist dist_ofList_iff ha (fun x hx => hM.of_mem hx) fun x hx => ?_
    have hl := l_lt_of_mem (xs := c :: cs) hx
    exact ih (l x) (by omega) le_rfl (ha.of_mem hx) (hM.of_mem hx)

/-! ### The main lemma (Arai, Lemma 1.33, for ϑ) -/

/-- The induction on the length of `γ ≺ ϑ α` in the main lemma. -/
theorem isAcc_of_lt_theta {α : ThetaTerm} (hM : Dist α)
    (hyp : ∀ ξ, NF ξ → Dist ξ → ξ < α → IsAcc (theta ξ)) :
    ∀ {γ : ThetaTerm}, NF γ → γ < theta α → IsAcc γ
  | Omega, _, h => absurd h (not_Omega_lt_theta α)
  | theta ξ, hγ, h => by
    rcases (theta_lt_theta_iff ξ α).mp h with ⟨h1, h2⟩ | ⟨g, hg, h3⟩
    · exact hyp ξ hγ.theta_arg
        (fun g hg => isAcc_of_lt_theta hM hyp (NF.of_mem_E hγ.theta_arg hg) (h2 g hg)) h1
    · exact (hM g hg).of_le hγ h3
  | sum xs, hγ, h => by
    have hxs : ∀ x ∈ xs, x < theta α := (sum_lt_prin_iff (isPrin_theta α) hγ.desc).mp h
    exact isAcc_of_toList hγ fun x hx => isAcc_of_lt_theta hM hyp (hγ.of_mem hx) (hxs x hx)
termination_by γ => l γ
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · exact l_lt_of_mem hx

/-- **Main lemma** (Arai, Lemma 1.33, adapted from `ψ` to `ϑ`): if `α` lies in the
distinguished class and `ϑ ξ` is accessible for every `ξ ≺ α` of the distinguished class, then
`ϑ α` is accessible. -/
theorem isAcc_theta_of_dist_of_forall {α : ThetaTerm} (hM : Dist α)
    (hyp : ∀ ξ, NF ξ → Dist ξ → ξ < α → IsAcc (theta ξ)) : IsAcc (theta α) :=
  Acc.intro _ fun _ ⟨hγ, _, h⟩ => isAcc_of_lt_theta hM hyp hγ h

/-- `ϑ` maps the distinguished class into the accessible part, by induction along `≺`
restricted to the distinguished class. -/
theorem isAcc_theta_of_dist {α : ThetaTerm} (hα : NF α) (hM : Dist α) : IsAcc (theta α) := by
  suffices ∀ a, Acc (RelOn Dist) a → NF a → Dist a → IsAcc (theta a) from
    this α (acc_dist _ le_rfl hα hM) hα hM
  intro a h
  induction h with
  | intro a _ ih =>
  intro _ hMa
  exact isAcc_theta_of_dist_of_forall hMa fun ξ hξ hMξ hlt => ih ξ ⟨hξ, hMξ, hlt⟩ hξ hMξ

/-! ### Every normal term is accessible -/

/-- Every normal term below `Ω` is accessible. -/
theorem isAcc_of_lt_Omega : ∀ {a : ThetaTerm}, NF a → a < Omega → IsAcc a
  | Omega, _, h => absurd h not_Omega_lt_Omega
  | theta ξ, ha, _ =>
    isAcc_theta_of_dist ha.theta_arg fun g hg =>
      isAcc_of_lt_Omega (NF.of_mem_E ha.theta_arg hg) (lt_Omega_of_mem_E hg)
  | sum xs, ha, h => by
    have hxs : ∀ x ∈ xs, x < Omega := (sum_lt_prin_iff isPrin_Omega ha.desc).mp h
    exact isAcc_of_toList ha fun x hx => isAcc_of_lt_Omega (ha.of_mem hx) (hxs x hx)
termination_by a => l a
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · exact l_lt_of_mem hx

/-- `Ω` is accessible. -/
theorem isAcc_Omega : IsAcc Omega :=
  Acc.intro _ fun _ ⟨hz, _, h⟩ => isAcc_of_lt_Omega hz h

/-- Every normal term of length at most `n` is accessible. -/
theorem isAcc_of_l_le : ∀ (n : ℕ) {a : ThetaTerm}, l a ≤ n → NF a → IsAcc a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a hn ha
  rcases lt_trichotomy' a Omega with h | rfl | h
  · exact isAcc_of_lt_Omega ha h
  · exact isAcc_Omega
  · obtain ⟨c, cs, rfl, _⟩ := Omega_lt_iff.mp h
    refine isAcc_of_toList ha fun x hx => ?_
    have hl := l_lt_of_mem (xs := c :: cs) hx
    exact ih (l x) (by omega) le_rfl (ha.of_mem hx)

/-- Every normal term is accessible. -/
theorem isAcc {a : ThetaTerm} (ha : NF a) : IsAcc a := isAcc_of_l_le _ le_rfl ha

/-- The order `≺` on normal terms is well founded (on raw terms, with predecessors taken among
the normal terms). -/
theorem wellFounded_rel : WellFounded Rel :=
  ⟨fun a => Acc.intro a fun _ ⟨hb, _, _⟩ => isAcc hb⟩

end ThetaTerm

namespace ThetaNote

/-- Every notation is accessible. -/
theorem acc (a : ThetaNote) : Acc (· < ·) a :=
  Subrelation.accessible (q := (· < ·)) (r := InvImage ThetaTerm.Rel Subtype.val)
    (fun {x _} h => ⟨x.2, trivial, h⟩)
    (InvImage.accessible Subtype.val (ThetaTerm.isAcc a.2))

/-- **The ϑ-order on normal terms is well founded.** -/
instance wellFoundedLT : WellFoundedLT ThetaNote := ⟨⟨acc⟩⟩

/-- The ϑ-notation as an ordinal notation system. -/
instance instOrdinalNotation : OrdinalNotation ThetaNote := ThetaNote.ordinalNotation

/-- The order type of all normal ϑ-terms. -/
noncomputable def orderType : Ordinal.{0} := Ordinal.type (α := ThetaNote) (· < ·)

/-- The Bachmann–Howard ordinal: the order type of the normal ϑ-terms below `Ω`. -/
noncomputable def bhOrdinal : Ordinal.{0} :=
  Ordinal.type (α := {a : ThetaNote // a < Omega}) (· < ·)

end ThetaNote

end OrdinalAnalysis
