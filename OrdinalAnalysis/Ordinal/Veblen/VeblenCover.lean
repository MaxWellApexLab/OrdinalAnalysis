/-
  U5: meta-level covers for the generalised descent `(D^β)`.

  This file collects, as theorems about `Gamma0Note`, the ordinal-notation facts that
  `gamma0_ramified_design.md` §1.3 uses when it builds `(D^β)` in the semiformal calculus
  `RA_∞`.  Every fact here is decided *in Lean, on `Gamma0Note`*: the external recursion is
  on the Lean-level index `β : Gamma0Note`, never on an internal object-level index, and
  nothing below needs the logical calculus at all — this is pure ordinal-notation
  mathematics.

  ### What is proved, and what is honestly left open

  §1.3's "Cover" bullet needs two families of facts, indexed by whether the Veblen level
  `a` is a successor or a limit, and inside each, by whether the height argument `h` is
  zero, a successor, or a limit (Step 2's case split). Working the mathematics out shows
  the cells are *not* all of equal difficulty:

  * **successor level, `h = 0` or `h` a successor** — closes completely on `Gamma0Note`,
    via mathlib's `Ordinal.deriv`/`Ordinal.nfp` for a *single* function `veblen β`
    (`veblen (β + 1) = deriv (veblen β)`, `deriv_zero_right`, `deriv_add_one`,
    `lt_nfp_iff`). The only witness produced is a natural number `m`, so there is no
    `Gamma0Note`-packaging issue at all.
  * **limit level, `h = 0`** — closes completely on `Gamma0Note` too, but by a different
    route: `veblen` at a limit level is `Ordinal.derivFamily` over *all* ordinals below the
    level, not a single function, so `deriv`/`nfp` do not apply directly. Instead the
    witness is read off `x`'s own syntax (`maxIndex`, the largest first-Veblen-argument used
    anywhere inside `x`), exactly the technique `RankSegments.lean` already uses for the
    omega-power hierarchy (its docstring: "`repr` is not surjective onto the ordinals below
    `Γ₀`, ... every witness produced here is read off the syntax instead"). This file's
    `limitCover_zero` is the two-argument analogue.
  * **`h` a limit, at either level** — genuinely open. The value `veblen a h` for `h` a
    limit is a supremum `⨆_{g < h} veblen a g` (`Order.IsNormal.lt_iff_exists_lt`), and the
    witness `g` it produces is an *ordinal* below `repr h`, not a `Gamma0Note`. Turning it
    into a `Gamma0Note` below `h` needs a fundamental-sequence assignment for `Gamma0Note`
    at an *arbitrary* limit — not a fixed, named ordinal such as `ε₀` (where
    `ACA/UpperBound.lean`'s `epsTower` already supplies one) — and no such assignment exists
    in the repository. This is exactly the gap `gamma0_ramified_design.md` §3.1 names under
    `InternalVebCover`'s "limit levels open": "What is missing is a `PR.Construction` for
    the sequence-indexed iterate ... ≈ 300–500 lines, MED [risk]," flagged there as a
    separately-scoped task. `succCover_limit_ordinal` and `limitCover_succ_ordinal` below
    state the true fact at the ordinal level (exactly what a fundamental-sequence assignment
    would need to feed into) and are documented as such; they are **not** restated with a
    `Gamma0Note` witness.
  * **limit level, `h` a successor** (the note's *main* case for limit `β`) — also open, for
    a sharper reason than a missing bridge lemma: at a limit level `a`,
    `veblen a (g + 1) = nfpFamily (family over all levels < a) (veblen a g + 1)`, so the
    number of "levels below `a`" actually used is an existential over a *finite list* of
    ordinals below `repr a` (`Ordinal.lt_nfpFamily_iff`), and — unlike the limit-level,
    `h = 0` case — this list cannot be bounded using `x`'s own syntax alone: taking
    `x := veblen β 0` for `β < a` and `h := 1` already forces `maxIndex x = β`, not `< β`,
    so no syntactic extraction of `x` alone can supply a level strictly below `a` once
    `h > 0`. This is a genuine mathematical obstruction, not a formalisation gap.

  So: the successor-level cover (task item (a)) is delivered in full for `h = 0`/`h`
  successor, with the `h`-limit edge case at the ordinal level; the limit-level cover
  (item (b)) is delivered in full for `h = 0` — the case the note's own §1.3 "Assemblies"
  actually uses ("the trivial base works ... climb is not needed") — with `h`
  successor/limit at the ordinal level. Item (c) (the zero/successor/limit case split on
  `h`) is proved for *every* `h : Gamma0Note`, with no gap. Item (d) (`λ_n` exhaustion) and
  item (e) (height arithmetic / monotonicity closure) are proved in full.

  ### Idiom

  Everything goes through `repr` and the existing `Gamma0Note` API (`Gamma0Note.lt_def`,
  `repr_veblenNote`, `repr_nadd_one`, `repr_omegaPow`) together with mathlib's
  `Ordinal.veblen`, `Ordinal.deriv`, `Ordinal.nfp`, `Ordinal.derivFamily` API, in the style
  of `RankSegments.lean` and `ACA/UpperBound.lean`.
-/
import OrdinalAnalysis.Ordinal.Veblen.RankSegments
import OrdinalAnalysis.Ordinal.Veblen.VeblenStructureInstance

set_option autoImplicit false

namespace OrdinalAnalysis

open Ordinal

/-! ### A pure ordinal-arithmetic lemma

Needed for the `h`-classification (item (c)): if `veblen p q ≠ 1` then `veblen p q` is a
limit ordinal (`isSuccLimit_of_isPrincipal_add`, since every Veblen value is additively
principal), and multiplying a limit ordinal by a positive natural keeps it a limit. -/
theorem isSuccLimit_mul_natCast {L : Ordinal} (hL : Order.IsSuccLimit L) :
    ∀ n : ℕ, 0 < n → Order.IsSuccLimit (L * n) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have heq : L * ((k + 1 : ℕ) : Ordinal) = L * (k : Ordinal) + L := by
    push_cast
    rw [mul_add, mul_one]
  rw [heq]
  exact isSuccLimit_add _ hL

/-- Every value of the Veblen function is either `1` (exactly at level `0`, argument `0`) or
a limit ordinal. -/
theorem veblen_eq_one_or_isSuccLimit (p q : Ordinal) :
    veblen p q = 1 ∨ Order.IsSuccLimit (veblen p q) := by
  have h1 : (1 : Ordinal) ≤ veblen p q := Order.one_le_iff_ne_zero.mpr veblen_pos.ne'
  rcases eq_or_lt_of_le h1 with h | h
  · exact Or.inl h.symm
  · exact Or.inr (isSuccLimit_of_isPrincipal_add h (isPrincipal_add_veblen p q))

namespace VNote

/-! ### Item (c): the zero/successor/limit case split on a Veblen notation

Read off the syntax by recursion on the trailing coefficient: `vadd a b n c` is a successor
iff `c` is (predecessor `vadd a b n c'` for `c`'s predecessor `c'`), and a limit iff `c = 0`
and `veblen (repr a) (repr b) ≠ 1`, or `c` is itself a limit. No surjectivity of `repr` is
used: every witness produced is an actual sub-notation of `x`. -/
theorem zero_or_exists_pred_or_isSuccLimit :
    ∀ x : VNote, NF x →
      x = 0 ∨ (∃ p, NF p ∧ repr p + 1 = repr x) ∨ Order.IsSuccLimit (repr x) := by
  intro x
  induction x with
  | zero => intro _; exact Or.inl rfl
  | vadd a b n c _ _ ihc =>
    intro hx
    rcases ihc hx.tail with hc0 | ⟨p, hp, hpc⟩ | hclim
    · -- `c = 0`
      subst hc0
      rcases veblen_eq_one_or_isSuccLimit (repr a) (repr b) with h1 | h1
      · -- `veblen (repr a) (repr b) = 1`, so `x` denotes the natural number `n`
        right; left
        refine ⟨VNote.ofNat ((n : ℕ) - 1), VNote.nf_ofNat _, ?_⟩
        have hn : 1 ≤ (n : ℕ) := n.property
        have hcast : ((n : ℕ) - 1 : ℕ) + 1 = (n : ℕ) := by omega
        rw [VNote.repr_ofNat, repr_vadd, repr_zero, add_zero, h1, one_mul]
        exact_mod_cast hcast
      · -- `veblen (repr a) (repr b)` is a limit, hence so is its finite multiple
        right; right
        rw [repr_vadd, repr_zero, add_zero]
        exact isSuccLimit_mul_natCast h1 (n : ℕ) n.property
    · -- `c` has predecessor `p`
      right; left
      have hp_lt_c : repr p < repr c := hpc ▸ lt_add_one (repr p)
      have hp_lt : repr p < veblen (repr a) (repr b) := hp_lt_c.trans hx.tail_lt
      refine ⟨VNote.vadd a b n p, NF.vadd hx.fst hx.snd hp hx.snd_lt hp_lt, ?_⟩
      simp only [repr_vadd]
      rw [← hpc, add_assoc]
    · -- `c` is a limit
      right; right
      rw [repr_vadd]
      exact isSuccLimit_add _ hclim

/-! ### `maxIndex`: the largest first-Veblen-argument used anywhere in a notation

The syntactic witness that replaces `derivFamily`'s abstract sup for the `h = 0` limit-index
cover (`Gamma0Note.limitCover_zero` below). -/

/-- Comparison-based maximum of two notations. Total, regardless of normality; correctness
(`repr_vmax`) needs both arguments normal. -/
def vmax (x y : VNote) : VNote :=
  if cmp x y = Ordering.lt then y else x

theorem repr_vmax {x y : VNote} (hx : NF x) (hy : NF y) :
    repr (vmax x y) = max (repr x) (repr y) := by
  have hcmp : cmp x y = _root_.cmp (repr x) (repr y) := cmp_eq_cmp_repr x y hx hy
  rw [vmax, hcmp]
  rcases lt_trichotomy (repr x) (repr y) with h | h | h
  · rw [h.cmp_eq_lt, if_pos rfl, max_eq_right h.le]
  · have hcond : _root_.cmp (repr x) (repr y) ≠ Ordering.lt := by
      rw [h, _root_.cmp_self_eq_eq]; simp
    rw [if_neg hcond, h, max_self]
  · rw [h.cmp_eq_gt, if_neg (by simp), max_eq_left h.le]

theorem nf_vmax {x y : VNote} (hx : NF x) (hy : NF y) : NF (vmax x y) := by
  rw [vmax]
  split_ifs with h
  · exact hy
  · exact hx

/-- The largest first-Veblen-argument occurring anywhere in `x`'s normal form, including
inside `x`'s second argument and tail. -/
def maxIndex : VNote → VNote
  | 0 => 0
  | vadd a b _ c => vmax a (vmax (maxIndex b) (maxIndex c))

theorem maxIndex_zero : maxIndex (0 : VNote) = 0 := rfl

theorem maxIndex_vadd (a b : VNote) (n : ℕ+) (c : VNote) :
    maxIndex (VNote.vadd a b n c) = vmax a (vmax (maxIndex b) (maxIndex c)) := rfl

theorem nf_maxIndex : ∀ {x : VNote}, NF x → NF (maxIndex x) := by
  intro x
  induction x with
  | zero => intro _; exact NF.zero
  | vadd a _ _ c _ ihb ihc =>
    intro hx
    exact nf_vmax hx.fst (nf_vmax (ihb hx.snd) (ihc hx.tail))

/-- The combined bound on `repr (maxIndex x)` in terms of `a`, `maxIndex b`, `maxIndex c`,
for `x = vadd a b n c`. -/
theorem repr_maxIndex_vadd {a b c : VNote} (n : ℕ+) (hx : NF (VNote.vadd a b n c)) :
    repr (maxIndex (VNote.vadd a b n c))
      = max (repr a) (max (repr (maxIndex b)) (repr (maxIndex c))) := by
  rw [maxIndex_vadd, repr_vmax hx.fst (nf_vmax (nf_maxIndex hx.snd) (nf_maxIndex hx.tail)),
    repr_vmax (nf_maxIndex hx.snd) (nf_maxIndex hx.tail)]

/-- **Unconditional upper bound.** Every notation `x` lies below `φ_{M+1}(h)` for `M` the
largest first-Veblen-argument occurring in `x`, whatever `h` is. -/
theorem repr_lt_veblen_maxIndex_succ :
    ∀ {x : VNote} (_ : NF x) (h : Ordinal), repr x < veblen (repr (maxIndex x) + 1) h := by
  intro x
  induction x with
  | zero => intro _ h; show (0 : Ordinal) < veblen ((0 : Ordinal) + 1) h; exact veblen_pos
  | vadd a b n c _ ihb ihc =>
    intro hx h
    have hMrepr := repr_maxIndex_vadd n hx
    have haM : repr a ≤ repr (maxIndex (VNote.vadd a b n c)) := by
      rw [hMrepr]; exact le_max_left _ _
    have hbM : repr (maxIndex b) ≤ repr (maxIndex (VNote.vadd a b n c)) := by
      rw [hMrepr]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hcM : repr (maxIndex c) ≤ repr (maxIndex (VNote.vadd a b n c)) := by
      rw [hMrepr]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hbM1 : repr (maxIndex b) + 1 ≤ repr (maxIndex (VNote.vadd a b n c)) + 1 :=
      add_le_add_left hbM 1
    have hcM1 : repr (maxIndex c) + 1 ≤ repr (maxIndex (VNote.vadd a b n c)) + 1 :=
      add_le_add_left hcM 1
    have hb : repr b < veblen (repr (maxIndex (VNote.vadd a b n c)) + 1) h :=
      (ihb hx.snd h).trans_le (veblen_left_monotone h hbM1)
    have hc : repr c < veblen (repr (maxIndex (VNote.vadd a b n c)) + 1) h :=
      (ihc hx.tail h).trans_le (veblen_left_monotone h hcM1)
    have haM1 : repr a < repr (maxIndex (VNote.vadd a b n c)) + 1 :=
      lt_of_le_of_lt haM (lt_add_one _)
    have hlead : veblen (repr a) (repr b)
        < veblen (repr (maxIndex (VNote.vadd a b n c)) + 1) h :=
      veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨haM1, hb⟩))
    have hL : IsPrincipal (· + ·) (veblen (repr (maxIndex (VNote.vadd a b n c)) + 1) h) :=
      isPrincipal_add_veblen _ _
    have hmul : veblen (repr a) (repr b) * (n : ℕ)
        < veblen (repr (maxIndex (VNote.vadd a b n c)) + 1) h :=
      hL.mul_natCast_lt hlead (n : ℕ)
    rw [repr_vadd]
    exact hL hmul hc

/-- **Necessary bound**, at `h = 0`: if `0 < β` and `x < φ_β(0)`, then `maxIndex x < β`. -/
theorem maxIndex_lt_of_lt_veblen_zero :
    ∀ {x : VNote} (_ : NF x) {β : Ordinal}, 0 < β → repr x < veblen β 0 →
      repr (maxIndex x) < β := by
  intro x
  induction x with
  | zero => intro _ β hβ _; show (0 : Ordinal) < β; exact hβ
  | vadd a b n c _ ihb ihc =>
    intro hx β hβ hlt
    have hlead_le : veblen (repr a) (repr b) ≤ repr (VNote.vadd a b n c) := by
      rw [repr_vadd]
      have h1 : (1 : Ordinal) ≤ (n : ℕ) := by exact_mod_cast n.property
      calc veblen (repr a) (repr b) = veblen (repr a) (repr b) * 1 := (mul_one _).symm
        _ ≤ veblen (repr a) (repr b) * (n : ℕ) := mul_le_mul_right h1 _
        _ ≤ veblen (repr a) (repr b) * (n : ℕ) + repr c := le_self_add
    have haβ : repr a < β := by
      by_contra hcon
      rw [not_lt] at hcon
      have h1 : veblen β 0 ≤ veblen (repr a) 0 := veblen_left_monotone 0 hcon
      have h2 : veblen (repr a) 0 ≤ veblen (repr a) (repr b) :=
        (veblen_right_strictMono (repr a)).monotone bot_le
      exact absurd hlt (not_lt.mpr (h1.trans (h2.trans hlead_le)))
    have hb0 : repr b < veblen β 0 := (hx.snd_lt.trans_le hlead_le).trans hlt
    have hc0 : repr c < veblen β 0 := (hx.tail_lt.trans_le hlead_le).trans hlt
    have hbβ : repr (maxIndex b) < β := ihb hx.snd hβ hb0
    have hcβ : repr (maxIndex c) < β := ihc hx.tail hβ hc0
    rw [repr_maxIndex_vadd n hx]
    exact max_lt haβ (max_lt hbβ hcβ)

end VNote

namespace Gamma0Note

/-! ### Item (c), for `Gamma0Note` -/

/-- **The zero/successor/limit case split** Step 2 of `(D^β)` performs on the height
parameter `h`. Every witness produced is an actual `Gamma0Note`; no surjectivity of `repr`
is used. -/
theorem zero_or_exists_pred_or_isSuccLimit (h : Gamma0Note) :
    h = 0 ∨ (∃ g : Gamma0Note, h = nadd g 1) ∨ Order.IsSuccLimit (repr h) := by
  rcases VNote.zero_or_exists_pred_or_isSuccLimit h.1 h.2 with h0 | ⟨p, hp, hpc⟩ | hlim
  · exact Or.inl (Subtype.ext h0)
  · have := hp
    refine Or.inr (Or.inl ⟨Gamma0Note.mk p, ?_⟩)
    apply repr_injective
    rw [repr_nadd_one, repr_mk]
    exact hpc.symm
  · exact Or.inr (Or.inr hlim)

/-! ### `maxIndexNote` -/

/-- The largest first-Veblen-argument occurring anywhere in `x`'s normal form. -/
def maxIndexNote (x : Gamma0Note) : Gamma0Note :=
  ⟨VNote.maxIndex x.1, VNote.nf_maxIndex x.2⟩

theorem repr_maxIndexNote (x : Gamma0Note) :
    repr (maxIndexNote x) = VNote.repr (VNote.maxIndex x.1) := rfl

/-- **Unconditional upper bound**, `Gamma0Note` version: every notation `x` lies below
`φ_{M ⊕ 1}(h)` for `M` the largest first-Veblen-argument occurring in `x`, whatever `h`
is. -/
theorem lt_veblenNote_nadd_maxIndexNote_one (x h : Gamma0Note) :
    x < veblenNote (nadd (maxIndexNote x) 1) h := by
  rw [lt_def, repr_veblenNote, repr_nadd_one]
  exact VNote.repr_lt_veblen_maxIndex_succ x.2 (repr h)

/-- **Necessary bound**, `Gamma0Note` version, at `h = 0`: if `0 < a` and `x < φ_a(0)`, then
`maxIndexNote x < a`. -/
theorem maxIndexNote_lt_of_lt_veblenNote_zero {a x : Gamma0Note} (ha : 0 < a)
    (hx : x < veblenNote a 0) : maxIndexNote x < a := by
  rw [lt_def, repr_maxIndexNote]
  have ha' : (0 : Ordinal) < repr a := by rw [lt_def, repr_zero] at ha; exact ha
  have hx' : repr x < veblen (repr a) 0 := by
    have h := hx; rw [lt_def, repr_veblenNote, repr_zero] at h; exact h
  exact VNote.maxIndex_lt_of_lt_veblen_zero x.2 ha' hx'

/-! ### Item (a): the successor-index cover -/

/-- Finite iteration of `φ_β`. -/
def phiIter (β : Gamma0Note) (m : ℕ) : Gamma0Note → Gamma0Note :=
  (veblenNote β)^[m]

theorem phiIter_zero (β : Gamma0Note) (c : Gamma0Note) : phiIter β 0 c = c := rfl

theorem phiIter_succ (β : Gamma0Note) (m : ℕ) (c : Gamma0Note) :
    phiIter β (m + 1) c = veblenNote β (phiIter β m c) :=
  Function.iterate_succ_apply' _ m c

theorem repr_phiIter (β : Gamma0Note) : ∀ (m : ℕ) (c : Gamma0Note),
    repr (phiIter β m c) = (fun y => veblen (repr β) y)^[m] (repr c)
  | 0, c => by rw [phiIter_zero]; rfl
  | (m + 1), c => by
      rw [phiIter_succ, repr_veblenNote, repr_phiIter β m c, Function.iterate_succ_apply']

/-- **Successor-index cover, `h = 0`.** Every `x < φ_{β ⊕ 1}(0)` lies below a finite iterate
of `φ_β` from `0`. -/
theorem succCover_zero {β x : Gamma0Note} (hx : x < veblenNote (nadd β 1) 0) :
    ∃ m : ℕ, x < phiIter β m 0 := by
  have h1 : repr x < veblen (repr β + 1) 0 := by
    have h := hx; rw [lt_def, repr_veblenNote, repr_nadd_one, repr_zero] at h; exact h
  rw [Ordinal.veblen_add_one, Ordinal.deriv_zero_right, Ordinal.lt_nfp_iff] at h1
  obtain ⟨m, hm⟩ := h1
  refine ⟨m, ?_⟩
  rw [lt_def, repr_phiIter]
  simpa using hm

/-- **Successor-index cover, `h` a successor** (the note's main case). Every
`x < φ_{β ⊕ 1}(g ⊕ 1)` lies below a finite iterate of `φ_β` from `φ_{β ⊕ 1}(g) ⊕ 1`. -/
theorem succCover_succ {β g x : Gamma0Note} (hx : x < veblenNote (nadd β 1) (nadd g 1)) :
    ∃ m : ℕ, x < phiIter β m (nadd (veblenNote (nadd β 1) g) 1) := by
  have h1 : repr x < veblen (repr β + 1) (repr g + 1) := by
    have h := hx
    rw [lt_def, repr_veblenNote, repr_nadd_one, repr_nadd_one] at h
    exact h
  rw [Ordinal.veblen_add_one, Ordinal.deriv_add_one, ← Ordinal.veblen_add_one] at h1
  rw [Ordinal.lt_nfp_iff] at h1
  obtain ⟨m, hm⟩ := h1
  refine ⟨m, ?_⟩
  rw [lt_def, repr_phiIter, repr_nadd_one, repr_veblenNote, repr_nadd_one]
  simpa using hm

/-- **Successor-index cover, `h` a limit — the ordinal-level statement.** `φ_{β ⊕ 1}` is
continuous at a limit `h`, so a bound below `φ_{β ⊕ 1}(h)` comes from some ordinal
`g' < repr h`. Turning `g'` into an actual `Gamma0Note` below `h` needs a
fundamental-sequence assignment for `Gamma0Note` at an *arbitrary* limit, which is not
developed in this file (see the module docstring); this is the honest statement of the fact
the note's edge case appeals to. -/
theorem succCover_limit_ordinal {β h x : Gamma0Note} (hh : Order.IsSuccLimit (repr h))
    (hx : x < veblenNote (nadd β 1) h) :
    ∃ g' : Ordinal, g' < repr h ∧ repr x < veblen (repr β + 1) g' := by
  have h1 : repr x < veblen (repr β + 1) (repr h) := by
    have h := hx; rw [lt_def, repr_veblenNote, repr_nadd_one] at h; exact h
  exact (Ordinal.isNormal_veblen (repr β + 1)).lt_iff_exists_lt hh |>.1 h1

/-! ### Item (b): the limit-index cover -/

/-- **Limit-index cover, `h = 0`.** For a limit level `a` and `x < φ_a(0)`, there is a level
`β'' < a` — read off `x`'s own syntax via `maxIndexNote` — with `x < φ_{β''}(0)`. This is
the case `gamma0_ramified_design.md` §1.3's "Assemblies" actually uses: "the trivial base
works ... climb is not needed." -/
theorem limitCover_zero {a x : Gamma0Note} (ha : Order.IsSuccLimit (repr a))
    (hx : x < veblenNote a 0) :
    ∃ β'' : Gamma0Note, β'' < a ∧ x < veblenNote β'' 0 := by
  have ha0 : (0 : Gamma0Note) < a := by rw [lt_def, repr_zero]; exact ha.pos
  have hMa : maxIndexNote x < a := maxIndexNote_lt_of_lt_veblenNote_zero ha0 hx
  refine ⟨nadd (maxIndexNote x) 1, ?_, lt_veblenNote_nadd_maxIndexNote_one x 0⟩
  have hsucc : Order.succ (repr (maxIndexNote x)) < repr a := ha.succ_lt (lt_def.mp hMa)
  rw [Order.succ_eq_add_one] at hsucc
  rw [lt_def, repr_nadd_one]
  exact hsucc

/-! ### Item (d): exhaustion of `Gamma0Note` by `λ_n`

`λ_0 := ε₀`, `λ_{n+1} := φ_{λ_n}(0)`, exactly as `gamma0_ramified_design.md` §1.3 defines
it. -/

/-- The sequence `λ_n` of §1.3's "Assemblies", used to exhaust `Gamma0Note` for the
autonomous statement. -/
def lam : ℕ → Gamma0Note
  | 0 => epsilonNote 0
  | (n + 1) => veblenNote (lam n) 0

@[simp] theorem lam_zero : lam 0 = epsilonNote 0 := rfl

theorem lam_succ (n : ℕ) : lam (n + 1) = veblenNote (lam n) 0 := rfl

theorem repr_lam : ∀ n : ℕ, repr (lam n) = (fun x : Ordinal => veblen x 0)^[n + 2] 0 := by
  intro n
  induction n with
  | zero =>
      have h2 : (fun x : Ordinal => veblen x 0)^[2] 0 = veblen (veblen 0 0) 0 := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one]
      show repr (lam 0) = (fun x : Ordinal => veblen x 0)^[0 + 2] 0
      rw [lam_zero, repr_epsilonNote, repr_zero, h2, veblen_zero_apply, opow_zero]
  | succ n ih =>
      show repr (lam (n + 1)) = (fun x : Ordinal => veblen x 0)^[(n + 1) + 2] 0
      rw [show (n + 1) + 2 = (n + 2) + 1 from rfl, Function.iterate_succ_apply']
      rw [lam_succ, repr_veblenNote, ih, repr_zero]

/-- **Every notation lies below some `λ_n`.** -/
theorem lt_lam (a : Gamma0Note) : ∃ n : ℕ, a < lam n := by
  obtain ⟨n, hn⟩ := Ordinal.lt_gamma_zero.1 (repr_lt_gamma_zero a)
  refine ⟨n, ?_⟩
  rw [lt_def, repr_lam n]
  have hmono : Monotone (fun k : ℕ => (fun x : Ordinal => veblen x 0)^[k] 0) := by
    apply monotone_nat_of_le_succ
    intro k
    rw [Function.iterate_succ_apply']
    exact left_le_veblen _ _
  exact hn.trans_le (hmono (by omega))

/-! ### Item (e): height arithmetic -/

/-- **Full comparison criterion for `veblenNote`**, the `Gamma0Note` transport of
`Ordinal.veblen_lt_veblen_iff`. -/
theorem veblenNote_lt_veblenNote_iff {a b a' b' : Gamma0Note} :
    veblenNote a b < veblenNote a' b' ↔
      (a = a' ∧ b < b') ∨ (a < a' ∧ b < veblenNote a' b') ∨ (a' < a ∧ veblenNote a b < b') := by
  simp only [lt_def, repr_veblenNote, ← repr_inj]
  exact veblen_lt_veblen_iff

/-- **`φ_β` does not escape `φ_a(z)`, for `β < a`.** The two-argument generalisation of
`Gamma0Note.omegaPow_lt_veblenNote` (the case `β = 0`) and `Gamma0Note.omegaPow_lt_epsilon`
(the case `a = 1`), both by transport along `repr` and `veblenNote_veblenNote_of_lt`. -/
theorem veblenNote_lt_veblenNote_of_lt {β a z y : Gamma0Note} (hβ : β < a)
    (hy : y < veblenNote a z) : veblenNote β y < veblenNote a z := by
  have hfix : veblenNote β (veblenNote a z) = veblenNote a z := veblenNote_veblenNote_of_lt hβ
  calc veblenNote β y < veblenNote β (veblenNote a z) := veblenNote_lt_veblenNote_right hy
    _ = veblenNote a z := hfix

/-- **Height closure**: iterating `omegaPow` finitely many times from below `ε₀` stays below
every `ε_a`. A `Gamma0Note` instance of the note's height bookkeeping ("`H(β) < ε_1` for
`β < ε₀`", `H(β) < λ` for `β < λ` an ε-number): any finite tower built from something below
`ε₀` is controlled by any `ε_a`. -/
theorem iterate_omegaPow_lt_epsilonNote {x : Gamma0Note} (hx : x < epsilonNote 0)
    (a : Gamma0Note) (k : ℕ) : (fun y => omegaPow y)^[k] x < epsilonNote a := by
  have h0a : (0 : Gamma0Note) ≤ a := by rw [le_def, repr_zero]; exact bot_le
  have hx' : x < epsilonNote a := lt_of_lt_of_le hx (epsilon_le_epsilon h0a)
  induction k with
  | zero => simpa using hx'
  | succ k ih => rw [Function.iterate_succ_apply']; exact omegaPow_lt_epsilon ih

end Gamma0Note

end OrdinalAnalysis
