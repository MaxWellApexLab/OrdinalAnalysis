/-
  Frontier track: the finite-function layer of Arai's ordinal analysis of Pi_N-Collection
  (arXiv 2311.12459v4) specialised to the shape needed by the Pi^1_2-CA_0 track.

  Covered (A4 numbering): Def 3.4 (finite functions, `f_c`, `f^c`, `g_c * f^c`, `<=`, `fld`, `f <^c xi`),
  Prop 3.6 (`ltC_mono`, with the corrected `tl mu <= tl lambda`), Def 3.24 (`irrB`), Def 3.25
  (`lxF`/`lxL`/`FF.lx`), Def 3.60 (`sTop`, `primeL`, `specialB`), Def 3.61 (`hbL`, `starSp`),
  the step-down side conditions of Def 3.31.6 / Cor 3.23 (`stepCond`).  Defs 3.1-3.3 (theta~, normal
  forms, segments, tails, theta~^{-c}) and Prop 3.5 are abstracted: the operations are the fields of
  `ThetaVal` / `ThetaShift`, the facts used are the fields of `ThetaLaws` / `ThetaInvLaws`.

  Generic over the ordinal-term type `alpha` (values) and the index type `iota`.  Representation: a
  finite function is a strictly sorted association list with non-zero values; every definition is a
  computable fuel-recursive `Bool`/`List` function (no well-founded recursion, no `Finsupp`, no choice),
  so `decide`/`#eval` run in the kernel.

  Main results (all from `ThetaLaws`; irreducibility gives the hypothesis `Tame`):
  * `lxL_irrefl`, `lxL_asymm`, `lxL_total` : `<_lx` is irreflexive, asymmetric and total on
    irreducible functions; `FF.lx_asymm`, `FF.lx_total` are the bundled forms;
  * `lxL_root`, `lxL_root_trans`, `lxL_root_total` : on root-type functions (supp <= 1, bounded value,
    A4 Def 3.31.5) `<_lx` is the lexicographic order on (support point, value), hence a strict linear
    order;
  * transitivity of `<_lx` on ALL irreducible functions is FALSE in general:
    `Nmodel.lx_not_transitive` in `FinFunModel.lean` (a lawful model with a 3-cycle).
-/
module

public import Mathlib.Order.Defs.LinearOrder

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace OrdinalAnalysis.Frontier

universe u v

/-- Value-side operations on the ordinal-term type `α` (A4 Def 3.2, 3.60-3.61).

* `oadd` : ordinal sum;
* `lam` : the base `Λ` of the `θ̃`-function (`K` in the specialisation);
* `tl` : tail `tl(ξ)` (principal, coefficient dropped);
* `segs ξ` : the segments of `ξ` (prefixes of the normal form, shortest first), A4 Def 3.2.1;
* `lamPred` : `Λ·(a+1) ↦ some (Λ·a)` and `none` on other arguments (A4 Def 3.60: the "room" `Λ`);
* `omegaMul` : `ξ ↦ ξ·ω`. -/
class ThetaVal (α : Type v) where
  oadd : α → α → α
  lam : α
  tl : α → α
  segs : α → List α
  lamPred : α → Option α
  omegaMul : α → α

/-- Gap-indexed operations: `th c c' ξ = θ̃_{c'-c}(ξ; Λ)` and `thInv c c' ξ = θ̃^{-(c'-c)}(ξ; Λ)`
(A4 Def 3.1, 3.2.2).  Indexing by the two endpoints avoids ordinal subtraction on `ι`. -/
class ThetaShift (ι : Type u) (α : Type v) where
  th : ι → ι → α → α
  thInv : ι → ι → α → α

namespace FinFun

variable {ι : Type u} {α : Type v}

section Defs

variable [LinearOrder ι] [LinearOrder α] [Zero α] [ThetaVal α] [ThetaShift ι α]

/-! ### Association lists -/

/-- The support points of an association list. -/
def keys (F : List (ι × α)) : List ι := F.map Prod.fst

/-- Value at `c` (`0` off the support). -/
def evL (F : List (ι × α)) (c : ι) : α :=
  match F.find? (fun p => decide (p.1 = c)) with
  | some p => p.2
  | none => 0

/-- strictly increasing keys -/
def Srt (F : List (ι × α)) : Prop := F.Pairwise (fun p q => p.1 < q.1)

/-- non-zero values -/
def NZ (F : List (ι × α)) : Prop := ∀ p ∈ F, p.2 ≠ 0

/-- `f^c`: the entries with key `≥ c` (A4 Def 3.4.1). -/
def tr (c : ι) (F : List (ι × α)) : List (ι × α) := F.filter (fun p => decide (c ≤ p.1))

/-- `f_c`: the entries with key `< c`. -/
def trLt (c : ι) (F : List (ι × α)) : List (ι × α) := F.filter (fun p => decide (p.1 < c))

/-- the entries with key `> c` -/
def above (F : List (ι × α)) (c : ι) : List (ι × α) := F.filter (fun p => decide (c < p.1))

/-- The first (smallest) key at which the two lists have different values. -/
def firstDiff : List (ι × α) → List (ι × α) → Option ι
  | [], [] => none
  | p :: _, [] => some p.1
  | [], q :: _ => some q.1
  | p :: F, q :: G =>
      if p.1 < q.1 then some p.1
      else if q.1 < p.1 then some q.1
      else if p.2 = q.2 then firstDiff F G else some p.1

/-- The shortest segment `µ` of `y` with `x < µ` (A4 Def 3.25.1/2); `y` itself if none. -/
def sh (x y : α) : α :=
  match (ThetaVal.segs y).find? (fun m => decide (x < m)) with
  | some m => m
  | none => y

/-- The relation `f <^b_lx g` of A4 Def 3.25, on the suffix lists `f^b`, `g^b`, with explicit fuel.
Case 1 (`f c < g c`): every support point `c'` of `f` above `c` with `tl µ ≤ θ̃_{c'-c}(f c')`
satisfies `f <^{c'}_lx g`.  Case 2 (`f c > g c`): some support point `c'` of `g` above `c` has
`f <^{c'}_lx g` and `tl ν ≤ θ̃_{c'-c}(g c')`.  Fuel `≥ |F| + |G|` suffices (`lxF_fuel`). -/
def lxF : Nat → List (ι × α) → List (ι × α) → Bool
  | 0, _, _ => false
  | n + 1, F, G =>
    match firstDiff F G with
    | none => false
    | some c =>
      if evL F c < evL G c then
        (above F c).all fun p =>
          !(decide (ThetaVal.tl (sh (evL F c) (evL G c)) ≤ ThetaShift.th c p.1 p.2))
            || lxF n (tr p.1 F) (tr p.1 G)
      else
        (above G c).any fun p =>
          decide (ThetaVal.tl (sh (evL G c) (evL F c)) ≤ ThetaShift.th c p.1 p.2)
            && lxF n (tr p.1 F) (tr p.1 G)

/-- `F <^b_lx G` with the canonical fuel. -/
def lxL (F G : List (ι × α)) : Bool := lxF (F.length + G.length) F G

/-! ### Basic lemmas on lookup -/

theorem evL_nil (c : ι) : evL ([] : List (ι × α)) c = 0 := rfl

theorem evL_cons (p : ι × α) (F : List (ι × α)) (c : ι) :
    evL (p :: F) c = if p.1 = c then p.2 else evL F c := by
  unfold evL
  by_cases h : p.1 = c <;> simp [List.find?_cons, h]

theorem evL_eq_zero_of_forall (F : List (ι × α)) (c : ι) (h : ∀ q ∈ F, q.1 ≠ c) :
    evL F c = 0 := by
  induction F with
  | nil => rfl
  | cons p F ih =>
    rw [evL_cons, if_neg (h p (List.mem_cons_self))]
    exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem evL_of_mem {F : List (ι × α)} (hS : Srt F) {c : ι} {v : α} (h : (c, v) ∈ F) :
    evL F c = v := by
  induction F with
  | nil => simp at h
  | cons p F ih =>
    rw [Srt, List.pairwise_cons] at hS
    rw [evL_cons]
    rcases List.mem_cons.1 h with h | h
    · have : p = (c, v) := h.symm
      subst this
      simp
    · have hlt := hS.1 (c, v) h
      rw [if_neg (ne_of_lt hlt)]
      exact ih hS.2 h

theorem mem_of_evL_ne {F : List (ι × α)} {c : ι} (h : evL F c ≠ 0) : (c, evL F c) ∈ F := by
  induction F with
  | nil => exact absurd rfl h
  | cons p F ih =>
    rw [evL_cons] at h ⊢
    by_cases hp : p.1 = c
    · rw [if_pos hp]
      have : p = (c, p.2) := Prod.ext hp rfl
      rw [← this]
      exact List.mem_cons_self
    · rw [if_neg hp] at h ⊢
      exact List.mem_cons_of_mem _ (ih h)

theorem key_of_evL_ne {F : List (ι × α)} {c : ι} (h : evL F c ≠ 0) : c ∈ keys F := by
  have := mem_of_evL_ne h
  exact List.mem_map.2 ⟨_, this, rfl⟩

theorem evL_tr {F : List (ι × α)} {c' e : ι} (h : c' ≤ e) : evL (tr c' F) e = evL F e := by
  unfold evL tr
  rw [List.find?_filter]
  have h2 : (fun a : ι × α => decide (decide (c' ≤ a.1) = true ∧ decide (a.1 = e) = true)) =
      fun a => decide (a.1 = e) := by
    funext a
    by_cases ha : a.1 = e <;> simp [ha, h]
  rw [h2]

/-! ### `firstDiff` -/

theorem firstDiff_symm (F G : List (ι × α)) : firstDiff G F = firstDiff F G := by
  induction F generalizing G with
  | nil => cases G <;> rfl
  | cons p F ih =>
    cases G with
    | nil => rfl
    | cons q G =>
      simp only [firstDiff]
      by_cases h1 : p.1 < q.1
      · simp [h1, not_lt_of_gt h1]
      · by_cases h2 : q.1 < p.1
        · simp [h1, h2]
        · have he : p.1 = q.1 := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
          by_cases h3 : p.2 = q.2
          · simp [h1, h2, h3, eq_comm, ih]
          · simp [h1, h2, h3, Ne.symm h3, he]

theorem firstDiff_mem {F G : List (ι × α)} {c : ι} (h : firstDiff F G = some c) :
    c ∈ keys F ∨ c ∈ keys G := by
  induction F generalizing G with
  | nil =>
    cases G with
    | nil => simp [firstDiff] at h
    | cons q G => simp [firstDiff] at h; subst h; simp [keys]
  | cons p F ih =>
    cases G with
    | nil => simp [firstDiff] at h; subst h; simp [keys]
    | cons q G =>
      simp only [firstDiff] at h
      by_cases h1 : p.1 < q.1
      · simp [h1] at h; subst h; simp [keys]
      · by_cases h2 : q.1 < p.1
        · simp [h1, h2] at h; subst h; simp [keys]
        · by_cases h3 : p.2 = q.2
          · simp [h1, h2, h3] at h
            rcases ih h with h | h
            · exact Or.inl (by simp [keys] at h ⊢; exact Or.inr h)
            · exact Or.inr (by simp [keys] at h ⊢; exact Or.inr h)
          · simp [h1, h2, h3] at h; subst h; simp [keys]

theorem firstDiff_none {F G : List (ι × α)} (h : firstDiff F G = none) :
    ∀ e, evL F e = evL G e := by
  induction F generalizing G with
  | nil =>
    cases G with
    | nil => intro e; rfl
    | cons q G => simp [firstDiff] at h
  | cons p F ih =>
    cases G with
    | nil => simp [firstDiff] at h
    | cons q G =>
      simp only [firstDiff] at h
      by_cases h1 : p.1 < q.1
      · simp [h1] at h
      · by_cases h2 : q.1 < p.1
        · simp [h1, h2] at h
        · by_cases h3 : p.2 = q.2
          · simp [h1, h2, h3] at h
            have he : p.1 = q.1 := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
            intro e
            rw [evL_cons, evL_cons, ← he, h3]
            by_cases hp : p.1 = e
            · simp [hp]
            · simp only [hp, if_false]; exact ih h e
          · simp [h1, h2, h3] at h


theorem lxF_eq_lt {n : Nat} {F G : List (ι × α)} {c : ι} (hfd : firstDiff F G = some c)
    (hlt : evL F c < evL G c) :
    lxF (n+1) F G = ((above F c).all fun p =>
      !(decide (ThetaVal.tl (sh (evL F c) (evL G c)) ≤ ThetaShift.th c p.1 p.2))
        || lxF n (tr p.1 F) (tr p.1 G)) := by
  simp only [lxF, hfd, if_pos hlt]

theorem lxF_eq_ge {n : Nat} {F G : List (ι × α)} {c : ι} (hfd : firstDiff F G = some c)
    (hge : ¬ evL F c < evL G c) :
    lxF (n+1) F G = ((above G c).any fun p =>
      decide (ThetaVal.tl (sh (evL G c) (evL F c)) ≤ ThetaShift.th c p.1 p.2)
        && lxF n (tr p.1 F) (tr p.1 G)) := by
  simp only [lxF, hfd, if_neg hge]

end Defs

/-! ### Laws -/

/-- The facts about the ordinal-term operations used by the proofs below.  Each field is a true
statement about `Γ(Λ)`-ordinals with their `θ̃`-normal forms (A4 Defs 3.1-3.2, Prop 3.5);
none of them is an assumption about finite functions. -/
class ThetaLaws (ι : Type u) (α : Type v) [LinearOrder ι] [LinearOrder α] [Zero α]
    [ThetaVal α] [ThetaShift ι α] : Prop where
  /-- `0` is least -/
  zero_le : ∀ x : α, 0 ≤ x
  /-- `θ̃_d` is monotone -/
  th_mono : ∀ (c c' : ι) (x y : α), x ≤ y → ThetaShift.th c c' x ≤ ThetaShift.th c c' y
  /-- `θ̃_{c''-c} = θ̃_{c'-c} ∘ θ̃_{c''-c'}` -/
  th_comp : ∀ (c c' c'' : ι) (x : α), c ≤ c' → c' ≤ c'' →
    ThetaShift.th c c'' x = ThetaShift.th c c' (ThetaShift.th c' c'' x)
  /-- `x ≤ x + y` -/
  le_oadd_left : ∀ x y : α, x ≤ ThetaVal.oadd x y
  /-- `y ≤ x + y` -/
  le_oadd_right : ∀ x y : α, y ≤ ThetaVal.oadd x y
  /-- `ξ` is a segment of itself -/
  self_mem_segs : ∀ x : α, x ∈ ThetaVal.segs x
  /-- a segment `µ` of `ξ` has `tl(ξ) ≤ tl(µ)` (the tail of a prefix is not smaller) -/
  tl_le_of_mem_segs : ∀ x m : α, m ∈ ThetaVal.segs x → ThetaVal.tl x ≤ ThetaVal.tl m
  /-- for `v ≠ 0` and `c < c'`: `Λ ≤ θ̃_{c'-c}(v)` -/
  lam_le_th : ∀ (c c' : ι) (v : α), v ≠ 0 → c < c' → ThetaVal.lam ≤ ThetaShift.th c c' v


section Order

variable [LinearOrder ι] [LinearOrder α] [Zero α] [ThetaVal α] [ThetaShift ι α]

/-- The tail condition that irreducibility gives (see `Irr.tame`): for two entries `c < c'`,
`θ̃_{c'-c}(f c') < tl(f c)`. -/
def Tame (F : List (ι × α)) : Prop :=
  ∀ p ∈ F, ∀ q ∈ F, p.1 < q.1 → ThetaShift.th p.1 q.1 q.2 < ThetaVal.tl p.2

theorem Srt.tr {F : List (ι × α)} (h : Srt F) (c : ι) : Srt (tr c F) :=
  List.Pairwise.sublist (List.filter_sublist) h

theorem NZ.tr {F : List (ι × α)} (h : NZ F) (c : ι) : NZ (tr c F) :=
  fun p hp => h p (List.mem_filter.1 hp).1

theorem Tame.tr {F : List (ι × α)} (h : Tame F) (c : ι) : Tame (tr c F) :=
  fun p hp q hq => h p (List.mem_filter.1 hp).1 q (List.mem_filter.1 hq).1

theorem firstDiff_ne {F G : List (ι × α)} (hF : Srt F) (hG : Srt G) (nF : NZ F) (nG : NZ G)
    {c : ι} (h : firstDiff F G = some c) : evL F c ≠ evL G c := by
  induction F generalizing G with
  | nil =>
    cases G with
    | nil => simp [firstDiff] at h
    | cons q G =>
      simp [firstDiff] at h
      subst h
      rw [evL_nil, evL_cons, if_pos rfl]
      exact fun e => nG q List.mem_cons_self e.symm
  | cons p F ih =>
    cases G with
    | nil =>
      simp [firstDiff] at h
      subst h
      rw [evL_nil, evL_cons, if_pos rfl]
      exact fun e => nF p List.mem_cons_self e
    | cons q G =>
      rw [Srt, List.pairwise_cons] at hF hG
      simp only [firstDiff] at h
      by_cases h1 : p.1 < q.1
      · simp [h1] at h
        subst h
        rw [evL_cons, if_pos rfl, evL_cons, if_neg (ne_of_lt h1).symm]
        have : evL G p.1 = 0 := by
          apply evL_eq_zero_of_forall
          intro r hr
          exact ne_of_gt (lt_trans h1 (hG.1 r hr))
        rw [this]
        exact nF p List.mem_cons_self
      · by_cases h2 : q.1 < p.1
        · simp [h1, h2] at h
          subst h
          rw [evL_cons, if_neg (ne_of_gt h2), evL_cons, if_pos rfl]
          have : evL F q.1 = 0 := by
            apply evL_eq_zero_of_forall
            intro r hr
            exact ne_of_gt (lt_trans h2 (hF.1 r hr))
          rw [this]
          exact fun e => nG q List.mem_cons_self e.symm
        · have he : p.1 = q.1 := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
          by_cases h3 : p.2 = q.2
          · simp [h1, h2, h3] at h
            have ih' := ih hF.2 hG.2 (fun r hr => nF r (List.mem_cons_of_mem _ hr))
              (fun r hr => nG r (List.mem_cons_of_mem _ hr)) h
            by_cases hc : p.1 = c
            · exfalso
              apply ih'
              have e1 : evL F c = 0 :=
                evL_eq_zero_of_forall _ _ (fun r hr => by rw [← hc]; exact ne_of_gt (hF.1 r hr))
              have e2 : evL G c = 0 :=
                evL_eq_zero_of_forall _ _
                  (fun r hr => by rw [← hc, he]; exact ne_of_gt (hG.1 r hr))
              rw [e1, e2]
            · rw [evL_cons, if_neg hc, evL_cons, if_neg (by rw [← he]; exact hc)]
              exact ih'
          · simp [h1, h2, h3] at h
            subst h
            rw [evL_cons, if_pos rfl, evL_cons, if_pos he.symm]
            exact h3

theorem len_tr_lt {F G : List (ι × α)} {c c' : ι} (hc : c ∈ keys F ∨ c ∈ keys G) (h : c < c') :
    (tr c' F).length + (tr c' G).length < F.length + G.length := by
  have h1 : (tr c' F).length ≤ F.length := List.length_filter_le _ _
  have h2 : (tr c' G).length ≤ G.length := List.length_filter_le _ _
  rcases hc with hc | hc
  · have : (tr c' F).length < F.length := by
      unfold tr
      rw [List.length_filter_lt_length_iff_exists]
      obtain ⟨a, hm, rfl⟩ := List.mem_map.1 hc
      exact ⟨a, hm, by simpa using h⟩
    omega
  · have : (tr c' G).length < G.length := by
      unfold tr
      rw [List.length_filter_lt_length_iff_exists]
      obtain ⟨a, hm, rfl⟩ := List.mem_map.1 hc
      exact ⟨a, hm, by simpa using h⟩
    omega

variable [ThetaLaws ι α]

include ι in
theorem sh_mem (x y : α) : sh x y ∈ ThetaVal.segs y := by
  unfold sh
  split
  · rename_i m hm
    exact List.mem_of_find?_eq_some hm
  · exact ThetaLaws.self_mem_segs ι y

include ι in
theorem tl_le_sh (x y : α) : ThetaVal.tl y ≤ ThetaVal.tl (sh x y) :=
  ThetaLaws.tl_le_of_mem_segs ι y _ (sh_mem (ι := ι) x y)

/-- Asymmetry and totality of `<_lx`, by one induction on the fuel. -/
theorem lxF_asym_total :
    ∀ (n : Nat) (F G : List (ι × α)), F.length + G.length ≤ n → Srt F → Srt G → NZ F → NZ G →
      Tame F → Tame G →
      ¬ (lxF n F G = true ∧ lxF n G F = true) ∧
      (firstDiff F G ≠ none → lxF n F G = true ∨ lxF n G F = true) := by
  intro n
  induction n with
  | zero =>
    intro F G hl _ _ _ _ _ _
    have hF : F = [] := List.length_eq_zero_iff.1 (by omega)
    have hG : G = [] := List.length_eq_zero_iff.1 (by omega)
    subst hF hG
    refine ⟨by simp [lxF], fun h => absurd (by simp [firstDiff]) h⟩
  | succ n ih =>
    -- the key step, for lists with first difference `c` and `F c < G c`
    have key : ∀ (F G : List (ι × α)), F.length + G.length ≤ n + 1 → Srt F → Srt G → NZ F →
        NZ G → Tame F → Tame G → ∀ c, firstDiff F G = some c → evL F c < evL G c →
        ¬ (lxF (n+1) F G = true ∧ lxF (n+1) G F = true) ∧
        (lxF (n+1) F G = true ∨ lxF (n+1) G F = true) := by
      intro F G hl hF hG nF nG tF tG c hfd hlt
      have hfd' : firstDiff G F = some c := by rw [firstDiff_symm]; exact hfd
      have hmem := firstDiff_mem hfd
      have hy : evL G c ≠ 0 := fun e => by
        have := ThetaLaws.zero_le ι (evL F c)
        rw [e] at hlt
        exact absurd hlt (not_lt.2 this)
      have eqL : lxF (n+1) F G = ((above F c).all fun p =>
          !(decide (ThetaVal.tl (sh (evL F c) (evL G c)) ≤ ThetaShift.th c p.1 p.2))
            || lxF n (tr p.1 F) (tr p.1 G)) := by
        simp only [lxF, hfd, if_pos hlt]
      have eqR : lxF (n+1) G F = ((above F c).any fun p =>
          decide (ThetaVal.tl (sh (evL F c) (evL G c)) ≤ ThetaShift.th c p.1 p.2)
            && lxF n (tr p.1 G) (tr p.1 F)) := by
        simp only [lxF, hfd', if_neg (not_lt_of_gt hlt)]
      have hlens : ∀ p ∈ above F c, (tr p.1 F).length + (tr p.1 G).length ≤ n := by
        intro p hp
        have hcp : c < p.1 := by simpa [above] using (List.mem_filter.1 hp).2
        have := len_tr_lt hmem hcp
        omega
      constructor
      · rintro ⟨h1, h2⟩
        rw [eqR] at h2
        obtain ⟨p, hp, hp2⟩ := List.any_eq_true.1 h2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hp2
        rw [eqL] at h1
        have h1' := List.all_eq_true.1 h1 p hp
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h1'
        have hpF : lxF n (tr p.1 F) (tr p.1 G) = true := by
          rcases h1' with h | h
          · exact absurd hp2.1 h
          · exact h
        exact (ih _ _ (hlens p hp) (hF.tr _) (hG.tr _) (nF.tr _) (nG.tr _) (tF.tr _) (tG.tr _)).1
          ⟨hpF, hp2.2⟩
      · by_cases hL : lxF (n+1) F G = true
        · exact Or.inl hL
        · right
          rw [eqL] at hL
          have hL' : ((above F c).all fun p =>
              !(decide (ThetaVal.tl (sh (evL F c) (evL G c)) ≤ ThetaShift.th c p.1 p.2))
                || lxF n (tr p.1 F) (tr p.1 G)) = false := by simpa using hL
          obtain ⟨p, hp, hp2⟩ := List.all_eq_false.1 hL'
          simp at hp2
          obtain ⟨habs, hnot⟩ := hp2
          have hpF : p ∈ F := (List.mem_filter.1 hp).1
          have hcp : c < p.1 := by simpa [above] using (List.mem_filter.1 hp).2
          have hdiff : firstDiff (tr p.1 F) (tr p.1 G) ≠ none := by
            intro hn
            have he := firstDiff_none hn p.1
            rw [evL_tr (le_refl _), evL_tr (le_refl _)] at he
            have hv : evL F p.1 = p.2 := evL_of_mem hF (by simpa using hpF)
            have hv0 : p.2 ≠ 0 := nF p hpF
            have hG1 : evL G p.1 ≠ 0 := by rw [← he, hv]; exact hv0
            have hGm := mem_of_evL_ne hG1
            have hGy := mem_of_evL_ne hy
            have hT := tG _ hGy _ hGm hcp
            rw [← he, hv] at hT
            exact absurd (le_trans (tl_le_sh (ι := ι) _ _) habs) (not_le.2 hT)
          have hT := (ih _ _ (hlens p hp) (hF.tr _) (hG.tr _) (nF.tr _) (nG.tr _) (tF.tr _)
            (tG.tr _)).2 hdiff
          rcases hT with hT | hT
          · rw [hnot] at hT; exact absurd hT (by simp)
          · rw [eqR]
            exact List.any_eq_true.2 ⟨p, hp, by simp [habs, hT]⟩
    intro F G hl hF hG nF nG tF tG
    cases hfd : firstDiff F G with
    | none =>
      refine ⟨?_, fun h => absurd rfl h⟩
      rintro ⟨h1, _⟩
      simp [lxF, hfd] at h1
    | some c =>
      have hne := firstDiff_ne hF hG nF nG hfd
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have k := key F G hl hF hG nF nG tF tG c hfd hlt
        exact ⟨k.1, fun _ => k.2⟩
      · have hfd' : firstDiff G F = some c := by rw [firstDiff_symm]; exact hfd
        have k := key G F (by omega) hG hF nG nF tG tF c hfd' hgt
        exact ⟨fun h => k.1 ⟨h.2, h.1⟩, fun _ => k.2.symm⟩

end Order


section Fuel

variable [LinearOrder ι] [LinearOrder α] [Zero α] [ThetaVal α] [ThetaShift ι α]

theorem all_congr' {β : Type*} (l : List β) (f g : β → Bool) (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem any_congr' {β : Type*} (l : List β) (f g : β → Bool) (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- The fuel `|F| + |G|` used by `lxL` is enough: more fuel changes nothing. -/
theorem lxF_stable : ∀ (n : Nat) (F G : List (ι × α)), F.length + G.length ≤ n →
    lxF n F G = lxF (n + 1) F G := by
  intro n
  induction n with
  | zero =>
    intro F G hl
    have hF : F = [] := List.length_eq_zero_iff.1 (by omega)
    have hG : G = [] := List.length_eq_zero_iff.1 (by omega)
    subst hF hG
    simp [lxF, firstDiff]
  | succ n ih =>
    intro F G hl
    cases hfd : firstDiff F G with
    | none => simp [lxF, hfd]
    | some c =>
      have hmem := firstDiff_mem hfd
      have hlens : ∀ p : ι × α, c < p.1 → (tr p.1 F).length + (tr p.1 G).length ≤ n := by
        intro p hcp
        have := len_tr_lt hmem hcp
        omega
      by_cases hlt : evL F c < evL G c
      · rw [lxF_eq_lt (n := n) hfd hlt, lxF_eq_lt (n := n + 1) hfd hlt]
        apply all_congr'
        intro p hp
        have hcp : c < p.1 := by simpa [above] using (List.mem_filter.1 hp).2
        rw [ih _ _ (hlens p hcp)]
      · rw [lxF_eq_ge (n := n) hfd hlt, lxF_eq_ge (n := n + 1) hfd hlt]
        apply any_congr'
        intro p hp
        have hcp : c < p.1 := by simpa [above] using (List.mem_filter.1 hp).2
        rw [ih _ _ (hlens p hcp)]

end Fuel

section Irr

variable [LinearOrder ι] [LinearOrder α] [Zero α] [ThetaVal α] [ThetaShift ι α]

/-- Irreducibility (A4 Def 3.24), computed from the top: for `p :: rest`, with `(c', cur)` the
merged value of `rest` (largest two entries merged first), require `tl(f c) > θ̃_{c'-c}(cur)` and
continue with `f c + θ̃_{c'-c}(cur)` as value at `c`.  Returns the head key and the merged value. -/
def irrStep (p : ι × α) : Option (ι × α) → Option (ι × α)
  | none => none
  | some (c', cur) =>
    if ThetaShift.th p.1 c' cur < ThetaVal.tl p.2 then
      some (p.1, ThetaVal.oadd p.2 (ThetaShift.th p.1 c' cur))
    else none

def irrFold : List (ι × α) → Option (ι × α)
  | [] => none
  | [p] => some p
  | p :: q :: rest => irrStep p (irrFold (q :: rest))

/-- `f` is irreducible (the empty function is). -/
def irrB (F : List (ι × α)) : Bool :=
  match F with
  | [] => true
  | _ :: _ => (irrFold F).isSome

variable [ThetaLaws ι α]

/-- Irreducibility bounds every entry: for `c ≤ c0` (the head key), `θ̃_{c'-c}(f c')` is below
the merged head value pushed down to `c`; and the entries satisfy `Tame`. -/
theorem irrFold_spec : ∀ (F : List (ι × α)), Srt F → ∀ (c0 : ι) (cur : α),
    irrFold F = some (c0, cur) →
    (∀ p rest, F = p :: rest → c0 = p.1) ∧
    (∀ q ∈ F, ∀ c : ι, c ≤ c0 → ThetaShift.th c q.1 q.2 ≤ ThetaShift.th c c0 cur) ∧ Tame F := by
  intro F
  induction F with
  | nil => intro _ c0 cur h; simp [irrFold] at h
  | cons p rest ih =>
    intro hS c0 cur h
    rw [Srt, List.pairwise_cons] at hS
    cases rest with
    | nil =>
      have h' : p = (c0, cur) := by simpa [irrFold] using h
      subst h'
      refine ⟨fun p' rest' e => ?_, ?_, ?_⟩
      · cases e; rfl
      · intro q hq c _
        simp at hq
        subst hq
        exact le_rfl
      · intro a ha b hb hab
        simp at ha hb
        subst ha hb
        exact absurd hab (lt_irrefl _)
    | cons q rest' =>
      have h' : irrStep p (irrFold (q :: rest')) = some (c0, cur) := h
      cases hq : irrFold (q :: rest') with
      | none => rw [hq] at h'; simp [irrStep] at h'
      | some r =>
        obtain ⟨c1, cur1⟩ := r
        rw [hq] at h'
        simp only [irrStep] at h'
        by_cases hlt : ThetaShift.th p.1 c1 cur1 < ThetaVal.tl p.2
        · rw [if_pos hlt] at h'
          simp only [Option.some.injEq, Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          obtain ⟨ih1, ih2, ih3⟩ := ih hS.2 c1 cur1 hq
          have hc1 : c1 = q.1 := ih1 q rest' rfl
          have hpq : p.1 < q.1 := hS.1 q List.mem_cons_self
          refine ⟨fun p' rest'' e => by simp at e; rw [e.1], ?_, ?_⟩
          · intro q' hq' c hc
            rcases List.mem_cons.1 hq' with e | e
            · subst e
              exact ThetaLaws.th_mono _ _ _ _ (ThetaLaws.le_oadd_left ι _ _)
            · have hle : p.1 ≤ q'.1 := le_of_lt (hS.1 q' e)
              rw [ThetaLaws.th_comp c p.1 q'.1 q'.2 hc hle]
              refine le_trans (ThetaLaws.th_mono _ _ _ _ ?_)
                (ThetaLaws.th_mono c p.1 _ _ (ThetaLaws.le_oadd_right ι _ _))
              exact ih2 q' e p.1 (by rw [hc1]; exact le_of_lt hpq)
          · intro a ha b hb hab
            rcases List.mem_cons.1 ha with ea | ea
            · subst ea
              rcases List.mem_cons.1 hb with eb | eb
              · subst eb; exact absurd hab (lt_irrefl _)
              · exact lt_of_le_of_lt
                  (ih2 b eb a.1 (by rw [hc1]; exact le_of_lt hpq)) hlt
            · rcases List.mem_cons.1 hb with eb | eb
              · subst eb; exact absurd hab (not_lt.2 (le_of_lt (hS.1 a ea)))
              · exact ih3 a ea b eb hab
        · rw [if_neg hlt] at h'
          simp at h'

theorem tame_of_irr {F : List (ι × α)} (hS : Srt F) (h : irrB F = true) : Tame F := by
  cases F with
  | nil => intro p hp; simp at hp
  | cons p rest =>
    simp only [irrB] at h
    cases hr : irrFold (p :: rest) with
    | none => rw [hr] at h; simp at h
    | some r => exact (irrFold_spec _ hS r.1 r.2 hr).2.2

end Irr


section Root

variable [LinearOrder ι] [LinearOrder α] [Zero α] [ThetaVal α] [ThetaShift ι α]

/-- `x` is bounded by the base: every segment has tail `≤ Λ` (`hd x ≤ Λ`).  This is the situation
of A4 Def 3.31.5 (`f(d) < K²`, tails in `{1, K}`). -/
def Bd (x : α) : Prop := ∀ m ∈ ThetaVal.segs x, ThetaVal.tl m ≤ ThetaVal.lam

/-- Root-type finite functions: at most one support point, bounded value (A4 Def 3.31.5). -/
def Root (F : List (ι × α)) : Prop := Srt F ∧ NZ F ∧ F.length ≤ 1 ∧ ∀ p ∈ F, Bd p.2

/-- Lexicographic order on (support point, value), empty function least. -/
def rootLt : List (ι × α) → List (ι × α) → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | p :: _, q :: _ => p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

theorem list_le_one {β : Type*} (l : List β) (h : l.length ≤ 1) : l = [] ∨ ∃ p, l = [p] := by
  match l, h with
  | [], _ => exact Or.inl rfl
  | [p], _ => exact Or.inr ⟨p, rfl⟩

variable [ThetaLaws ι α]

theorem lxF_nil_cons (q : ι × α) (hq : q.2 ≠ 0) : lxF 1 [] [q] = true := by
  have hfd : firstDiff ([] : List (ι × α)) [q] = some q.1 := by simp [firstDiff]
  have h0 : evL ([] : List (ι × α)) q.1 < evL [q] q.1 := by
    rw [evL_nil, evL_cons, if_pos rfl]
    exact lt_of_le_of_ne (ThetaLaws.zero_le ι _) (Ne.symm hq)
  rw [lxF_eq_lt (n := 0) hfd h0]
  simp [above]

theorem lxF_cons_nil (p : ι × α) : lxF 1 [p] [] = false := by
  have hfd : firstDiff [p] ([] : List (ι × α)) = some p.1 := by simp [firstDiff]
  have h0 : ¬ evL [p] p.1 < evL ([] : List (ι × α)) p.1 := by
    rw [evL_nil, evL_cons, if_pos rfl]
    exact not_lt.2 (ThetaLaws.zero_le ι _)
  rw [lxF_eq_ge (n := 0) hfd h0]
  simp [above]

include ι in
theorem lxL_root {F G : List (ι × α)} (hF : Root F) (hG : Root G) :
    lxL F G = true ↔ rootLt F G := by
  obtain ⟨sF, nF, lF, bF⟩ := hF
  obtain ⟨sG, nG, lG, bG⟩ := hG
  rcases list_le_one F lF with rfl | ⟨p, rfl⟩ <;> rcases list_le_one G lG with rfl | ⟨q, rfl⟩
  · simp [lxL, lxF, rootLt]
  · have hq : q.2 ≠ 0 := nG q List.mem_cons_self
    simp only [lxL, rootLt, List.length_nil, List.length_cons, iff_true]
    exact lxF_nil_cons q hq
  · have hp : p.2 ≠ 0 := nF p List.mem_cons_self
    simp only [lxL, rootLt, List.length_nil, List.length_cons, iff_false]
    simp [lxF_cons_nil p]
  · have hp : p.2 ≠ 0 := nF p List.mem_cons_self
    have hq : q.2 ≠ 0 := nG q List.mem_cons_self
    have bp : Bd p.2 := bF p List.mem_cons_self
    have bq : Bd q.2 := bG q List.mem_cons_self
    simp only [lxL, List.length_cons, List.length_nil, rootLt]
    rcases lt_trichotomy p.1 q.1 with h | h | h
    · -- p.1 < q.1: the empty-vs-singleton comparison at q.1 decides
      have hfd : firstDiff [p] [q] = some p.1 := by simp [firstDiff, h]
      have hv1 : evL [p] p.1 = p.2 := by rw [evL_cons, if_pos rfl]
      have hv2 : evL [q] p.1 = 0 := by rw [evL_cons, if_neg (ne_of_lt h).symm]; rfl
      have hge : ¬ evL [p] p.1 < evL [q] p.1 := by
        rw [hv2]; exact not_lt.2 (ThetaLaws.zero_le ι _)
      rw [show (0 + 1 + 1) = 1 + 1 from rfl]
      rw [lxF_eq_ge (n := 1) hfd hge]
      have habs : ThetaVal.tl (sh (evL [q] p.1) (evL [p] p.1)) ≤ ThetaShift.th p.1 q.1 q.2 := by
        rw [hv1, hv2]
        exact le_trans (bp _ (sh_mem (ι := ι) 0 p.2)) (ThetaLaws.lam_le_th p.1 q.1 q.2 hq h)
      have htr1 : tr q.1 [p] = [] := by simp [tr, not_le.2 h]
      have htr2 : tr q.1 [q] = [q] := by simp [tr]
      have habove : above [q] p.1 = [q] := by simp [above, h]
      simp only [habove, htr1, htr2, List.any_cons, List.any_nil, Bool.or_false]
      rw [lxF_nil_cons q hq]
      simp [habs, h]
    · -- p.1 = q.1
      by_cases h3 : p.2 = q.2
      · have hfd : firstDiff [p] [q] = none := by
          simp [firstDiff, h, h3, lt_irrefl]
        have : lxF (0 + 1 + 1) [p] [q] = false := by simp [lxF, hfd]
        rw [this]
        simp [h, h3]
      · have hfd : firstDiff [p] [q] = some p.1 := by simp [firstDiff, h, h3]
        have hv1 : evL [p] p.1 = p.2 := by rw [evL_cons, if_pos rfl]
        have hv2 : evL [q] p.1 = q.2 := by rw [evL_cons, if_pos h.symm]
        rw [show (0 + 1 + 1) = 1 + 1 from rfl]
        by_cases hlt : p.2 < q.2
        · rw [lxF_eq_lt (n := 1) hfd (by rw [hv1, hv2]; exact hlt)]
          simp [above, h, hlt]
        · rw [lxF_eq_ge (n := 1) hfd (by rw [hv1, hv2]; exact hlt)]
          simp [above, h, hlt]
    · -- q.1 < p.1
      have hfd : firstDiff [p] [q] = some q.1 := by
        simp [firstDiff, not_lt.2 (le_of_lt h), h]
      have hv1 : evL [p] q.1 = 0 := by rw [evL_cons, if_neg (ne_of_gt h)]; rfl
      have hv2 : evL [q] q.1 = q.2 := by rw [evL_cons, if_pos rfl]
      have hlt : evL [p] q.1 < evL [q] q.1 := by
        rw [hv1, hv2]; exact lt_of_le_of_ne (ThetaLaws.zero_le ι _) (Ne.symm hq)
      rw [show (0 + 1 + 1) = 1 + 1 from rfl]
      rw [lxF_eq_lt (n := 1) hfd hlt]
      have habs : ThetaVal.tl (sh (evL [p] q.1) (evL [q] q.1)) ≤ ThetaShift.th q.1 p.1 p.2 := by
        rw [hv1, hv2]
        exact le_trans (bq _ (sh_mem (ι := ι) 0 q.2)) (ThetaLaws.lam_le_th q.1 p.1 p.2 hp h)
      have htr1 : tr p.1 [p] = [p] := by simp [tr]
      have htr2 : tr p.1 [q] = [] := by simp [tr, not_le.2 h]
      have habove : above [p] q.1 = [p] := by simp [above, h]
      simp only [habove, htr1, htr2, List.all_cons, List.all_nil, Bool.and_true]
      rw [lxF_cons_nil p]
      simp [habs, not_lt.2 (le_of_lt h), (ne_of_gt h)]

theorem rootLt_irrefl (F : List (ι × α)) : ¬ rootLt F F := by
  cases F with
  | nil => simp [rootLt]
  | cons p F => simp [rootLt]

theorem rootLt_trans {F G H : List (ι × α)} (h1 : rootLt F G) (h2 : rootLt G H) :
    rootLt F H := by
  cases F with
  | nil =>
    cases H with
    | nil => cases G <;> simp_all [rootLt]
    | cons r H => simp [rootLt]
  | cons p F =>
    cases G with
    | nil => simp [rootLt] at h1
    | cons q G =>
      cases H with
      | nil => simp [rootLt] at h2
      | cons r H =>
        simp only [rootLt] at h1 h2 ⊢
        rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
        · exact Or.inl (lt_trans h1 h2)
        · exact Or.inl (h2 ▸ h1)
        · exact Or.inl (h1 ▸ h2)
        · exact Or.inr ⟨h1.trans h2, lt_trans h1' h2'⟩

theorem rootLt_total {F G : List (ι × α)} (hF : F.length ≤ 1) (hG : G.length ≤ 1) (hne : F ≠ G) :
    rootLt F G ∨ rootLt G F := by
  rcases list_le_one F hF with rfl | ⟨p, rfl⟩ <;> rcases list_le_one G hG with rfl | ⟨q, rfl⟩
  · exact absurd rfl hne
  · exact Or.inl (by simp [rootLt])
  · exact Or.inr (by simp [rootLt])
  · simp only [rootLt]
    rcases lt_trichotomy p.1 q.1 with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases lt_trichotomy p.2 q.2 with h' | h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact absurd (by rw [Prod.ext h h']) hne
      · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
    · exact Or.inr (Or.inl h)


end Root


/-! ### Public statements for `<_lx` on association lists -/

section LxPublic

variable [LinearOrder ι] [LinearOrder α] [Zero α] [ThetaVal α] [ThetaShift ι α]

theorem firstDiff_self (F : List (ι × α)) : firstDiff F F = none := by
  induction F with
  | nil => rfl
  | cons p F ih => simp [firstDiff, ih, lt_irrefl]

theorem lxF_self (n : Nat) (F : List (ι × α)) : lxF n F F = false := by
  cases n with
  | zero => rfl
  | succ n => simp [lxF, firstDiff_self]

/-- Irreflexivity of `<_lx`. -/
theorem lxL_irrefl (F : List (ι × α)) : lxL F F = false := lxF_self _ F

variable [ThetaLaws ι α]

include ι in
/-- Asymmetry of `<_lx` (on sorted, nonzero, tame lists; irreducible lists are tame). -/
theorem lxL_asymm {F G : List (ι × α)} (hF : Srt F) (hG : Srt G) (nF : NZ F) (nG : NZ G)
    (tF : Tame F) (tG : Tame G) : ¬ (lxL F G = true ∧ lxL G F = true) := by
  have := (lxF_asym_total (F.length + G.length) F G (Nat.le_refl _) hF hG nF nG tF tG).1
  unfold lxL
  rw [Nat.add_comm G.length F.length]
  exact this

include ι in
/-- Totality (trichotomy) of `<_lx`: two lists that differ are comparable. -/
theorem lxL_total {F G : List (ι × α)} (hF : Srt F) (hG : Srt G) (nF : NZ F) (nG : NZ G)
    (tF : Tame F) (tG : Tame G) (hd : ∃ e, evL F e ≠ evL G e) :
    lxL F G = true ∨ lxL G F = true := by
  have hfd : firstDiff F G ≠ none := by
    intro hn
    obtain ⟨e, he⟩ := hd
    exact he (firstDiff_none hn e)
  have := (lxF_asym_total (F.length + G.length) F G (Nat.le_refl _) hF hG nF nG tF tG).2 hfd
  unfold lxL
  rw [Nat.add_comm G.length F.length]
  exact this

end LxPublic

/-! ### Bundled finite functions -/

/-- A finite function `f : ι → α` with finite support: a strictly sorted association list with
non-zero values (A4 Def 3.4.1, without the normal-form restriction on the values, which belongs to
the ordinal-term type). -/
structure FF (ι : Type u) (α : Type v) [LinearOrder ι] [LinearOrder α] [Zero α] where
  l : List (ι × α)
  srt : Srt l
  nz : NZ l

namespace FF

section Basic

variable [LinearOrder ι] [LinearOrder α] [Zero α] [ThetaVal α] [ThetaShift ι α]

/-- `f(c)` -/
def ev (f : FF ι α) (c : ι) : α := evL f.l c

/-- `supp f` -/
def supp (f : FF ι α) : List ι := keys f.l

/-- `fld f` = supports and values (A4 Def 3.4.1) -/
def fld (f : FF ι α) : List ι × List α := (f.l.map Prod.fst, f.l.map Prod.snd)

/-- irreducible (A4 Def 3.24) -/
def Irr (f : FF ι α) : Prop := irrB f.l = true

/-- `f <^b_lx g` (A4 Def 3.25) -/
def lx (f g : FF ι α) (b : ι) : Bool := lxL (tr b f.l) (tr b g.l)

/-- the empty function -/
def empty : FF ι α := ⟨[], List.Pairwise.nil, fun _ h => by simp at h⟩

theorem lx_irrefl (f : FF ι α) (b : ι) : f.lx f b = false := lxL_irrefl _

variable [ThetaLaws ι α]

include ι in
theorem lx_asymm {f g : FF ι α} (hf : f.Irr) (hg : g.Irr) (b : ι) :
    ¬ (f.lx g b = true ∧ g.lx f b = true) :=
  lxL_asymm (f.srt.tr b) (g.srt.tr b) (f.nz.tr b) (g.nz.tr b)
    ((tame_of_irr f.srt hf).tr b) ((tame_of_irr g.srt hg).tr b)

include ι in
/-- Trichotomy: `f^b ≠ g^b` implies `f <^b_lx g` or `g <^b_lx f`. -/
theorem lx_total {f g : FF ι α} (hf : f.Irr) (hg : g.Irr) (b : ι)
    (hd : ∃ e, b ≤ e ∧ f.ev e ≠ g.ev e) : f.lx g b = true ∨ g.lx f b = true := by
  obtain ⟨e, hbe, he⟩ := hd
  refine lxL_total (f.srt.tr b) (g.srt.tr b) (f.nz.tr b) (g.nz.tr b)
    ((tame_of_irr f.srt hf).tr b) ((tame_of_irr g.srt hg).tr b) ⟨e, ?_⟩
  rw [evL_tr hbe, evL_tr hbe]
  exact he

end Basic

end FF

/-! ### `f <^c ξ` (A4 Def 3.4.2) and Prop 3.5/3.6 -/

section LtC

variable [LinearOrder ι] [LinearOrder α] [Zero α] [ThetaVal α] [ThetaShift ι α]

/-- `f <^c_Λ ξ` with explicit fuel: `f^c = ∅` holds; with no support point above `c` it means
`f c < ξ`; otherwise some segment `µ` of `ξ` has `f c < µ` and `f <^{c'} θ̃^{-(c'-c)}(tl µ)` for the
next support point `c'` above `c`. -/
def ltCF (F : List (ι × α)) : Nat → ι → α → Bool
  | 0, _, _ => false
  | n + 1, c, ξ =>
    if (tr c F).isEmpty then true
    else
      match above F c with
      | [] => decide (evL F c < ξ)
      | p :: _ =>
        (ThetaVal.segs ξ).any fun m =>
          decide (evL F c < m)
            && ltCF F n p.1 (ThetaShift.thInv c p.1 (ThetaVal.tl m))

/-- `f <^c ξ` with sufficient fuel. -/
def ltC (F : List (ι × α)) (c : ι) (ξ : α) : Bool := ltCF F (F.length + 1) c ξ

/-- Prop 3.5.1/3.5.2 and the segment extension used in Prop 3.6. -/
class ThetaInvLaws (ι : Type u) (α : Type v) [LinearOrder ι] [LinearOrder α] [Zero α]
    [ThetaVal α] [ThetaShift ι α] : Prop where
  /-- Prop 3.5.1: `ζ ≤ ξ → θ̃^{-d}(ζ) ≤ θ̃^{-d}(ξ)` -/
  thInv_mono : ∀ (c c' : ι) (x y : α), x ≤ y → ThetaShift.thInv c c' x ≤ ThetaShift.thInv c c' y
  /-- Prop 3.5.2: `θ̃_d(θ̃^{-d}(ζ)) ≤ ζ` -/
  th_thInv_le : ∀ (c c' : ι) (x : α), ThetaShift.th c c' (ThetaShift.thInv c c' x) ≤ x
  /-- if `µ` is a segment of `ξ ≤ ζ`, some segment `λ` of `ζ` has `µ ≤ λ` and `tl µ ≤ tl λ`
  (the proof of Prop 3.6; the printed `tl µ < tl λ` is the slip corrected in
  `pi12ca0_specialisation.md` §4.3) -/
  segs_ext : ∀ x z m : α, x ≤ z → m ∈ ThetaVal.segs x →
    ∃ l ∈ ThetaVal.segs z, m ≤ l ∧ ThetaVal.tl m ≤ ThetaVal.tl l

theorem ltCF_mono [ThetaInvLaws ι α] (F : List (ι × α)) :
    ∀ (n : Nat) (c : ι) (x z : α), x ≤ z → ltCF F n c x = true → ltCF F n c z = true := by
  intro n
  induction n with
  | zero => intro c x z _ h; simp [ltCF] at h
  | succ n ih =>
    intro c x z hxz h
    simp only [ltCF] at h ⊢
    by_cases he : (tr c F).isEmpty = true
    · simp [he]
    · rw [if_neg he] at h ⊢
      cases hab : above F c with
      | nil =>
        rw [hab] at h
        simp only [decide_eq_true_eq] at h ⊢
        exact lt_of_lt_of_le h hxz
      | cons p rest =>
        rw [hab] at h
        simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
        obtain ⟨m, hm, hlt, hrec⟩ := h
        obtain ⟨l, hl, hml, htl⟩ := ThetaInvLaws.segs_ext ι x z m hxz hm
        exact ⟨l, hl, ⟨lt_of_lt_of_le hlt hml, ih _ _ _ (ThetaInvLaws.thInv_mono _ _ _ _ htl) hrec⟩⟩

/-- Prop 3.6 (with the corrected `tl µ ≤ tl λ`): `f <^c ξ ≤ ζ → f <^c ζ`. -/
theorem ltC_mono [ThetaInvLaws ι α] (F : List (ι × α)) (c : ι) {x z : α} (hxz : x ≤ z)
    (h : ltC F c x = true) : ltC F c z = true :=
  ltCF_mono F _ c x z hxz h

end LtC


/-! ### Root-type functions: `<_lx` is a strict linear order -/

section RootOrder

variable [LinearOrder ι] [LinearOrder α] [Zero α] [ThetaVal α] [ThetaShift ι α] [ThetaLaws ι α]

include ι in
/-- On root-type functions `<_lx` is transitive (A4 Lemma 3.37 restricted to Def 3.31.5). -/
theorem lxL_root_trans {F G H : List (ι × α)} (hF : Root F) (hG : Root G) (hH : Root H)
    (h1 : lxL F G = true) (h2 : lxL G H = true) : lxL F H = true :=
  (lxL_root hF hH).2 (rootLt_trans ((lxL_root hF hG).1 h1) ((lxL_root hG hH).1 h2))

include ι in
/-- On root-type functions `<_lx` is total. -/
theorem lxL_root_total {F G : List (ι × α)} (hF : Root F) (hG : Root G) (hne : F ≠ G) :
    lxL F G = true ∨ lxL G F = true := by
  rcases rootLt_total hF.2.2.1 hG.2.2.1 hne with h | h
  · exact Or.inl ((lxL_root hF hG).2 h)
  · exact Or.inr ((lxL_root hG hF).2 h)

end RootOrder

/-! ### Special functions, `h_b(g; a)`, concatenation (A4 Defs 3.60, 3.61) -/

section Special

variable [LinearOrder ι] [LinearOrder α] [Zero ι] [Zero α] [ThetaVal α] [ThetaShift ι α]

/-- `s(f) = max({0} ∪ supp f)` (A4 Def 3.60). -/
def sTop (F : List (ι × α)) : ι := (F.getLast?.map Prod.fst).getD 0

/-- the primed function `f'`: the top value `Λ(α+1)` replaced by `Λ·α` (A4 Def 3.60). -/
def primeL (F : List (ι × α)) : List (ι × α) :=
  match F.getLast? with
  | none => F
  | some p => F.dropLast ++ [(p.1, (ThetaVal.lamPred p.2).getD p.2)]

/-- inverse of `primeL` on special functions: the top value `Λ·α` becomes `Λ·α + Λ = Λ(α+1)`. -/
def unprimeL (F : List (ι × α)) : List (ι × α) :=
  match F.getLast? with
  | none => F
  | some p => F.dropLast ++ [(p.1, ThetaVal.oadd p.2 ThetaVal.lam)]

/-- `f` is special: non-empty, irreducible, and its top value has the form `Λ(α+1)`
(A4 Def 3.60). -/
def specialB (F : List (ι × α)) : Bool :=
  irrB F && !F.isEmpty && (F.getLast?.bind fun p => ThetaVal.lamPred p.2).isSome

/-- `h_b(g; a)` for a special `g` and `b ≤ s(g)` (A4 Def 3.61.1): `h_b = g_b`, `s(h) = b` and
`h(b) = α₀ + Λ` where `α_n = g'(s(g)) + a`, `α_i = g(b_i) + θ̃_{b_{i+1}-b_i}(α_{i+1})` along
`{b = b₀ < b₁ < … < b_n = s(g)} = {b, s(g)} ∪ ((b, s(g)) ∩ supp g)`.  For `b = s(g)`, and for
`b > s(g)` (outside the definition), the result is `g`. -/
def hbL (g : List (ι × α)) (b : ι) (a : α) : List (ι × α) :=
  let s := sTop g
  if b < s then
    let mids := (g.filter fun p => decide (b < p.1 ∧ p.1 < s)).map Prod.fst
    let top := ((ThetaVal.lamPred (evL g s)).getD (evL g s))
    let r := (b :: mids).foldr
      (fun bi (acc : ι × α) =>
        (bi, ThetaVal.oadd (evL g bi) (ThetaShift.th bi acc.1 acc.2)))
      (s, ThetaVal.oadd top a)
    trLt b g ++ [(b, ThetaVal.oadd r.2 ThetaVal.lam)]
  else g

/-- the concatenation `g_c ∗ f^c` of A4 Def 3.4.1. -/
def catL (g f : List (ι × α)) (c : ι) : List (ι × α) := trLt c g ++ tr c f

/-- `f_b ∗ g^b` for special functions (A4 Def 3.61.2): the special function `h` with
`h'(c) = f'(c)` for `c < b` and `h'(c) = g'(c)` for `c ≥ b`.  (A zero value of `f'` at `s(f)` is
dropped when something above it remains: it is no longer in the support.) -/
def starSp (f g : List (ι × α)) (b : ι) : List (ι × α) :=
  let lo := trLt b (primeL f)
  let hi := tr b (primeL g)
  if hi.isEmpty then unprimeL lo
  else unprimeL (lo.filter (fun p => decide (p.2 ≠ 0)) ++ hi)

/-- The step-down side conditions of A4 Def 3.31.6 / Cor 3.23 (specialised to `N = 1`):
`d < c ∈ supp f`, `(d,c) ∩ supp f = ∅`, `g_d ≤ f_d`, `(d,c) ∩ supp g = ∅`,
`g(d) < f(d) + θ̃_{c-d}(f(c))·ω` and `g <^c f(c)`.  Irreducibility of `g` is a separate hypothesis
(`irrB g`). -/
def stepCond (g f : List (ι × α)) (d c : ι) : Bool :=
  decide (d < c) && (keys f).contains c
    && (f.all fun p => decide (¬ (d < p.1 ∧ p.1 < c)))
    && ((trLt d g).all fun p => decide (p.2 ≤ evL f p.1))
    && (g.all fun p => decide (¬ (d < p.1 ∧ p.1 < c)))
    && decide (evL g d < ThetaVal.oadd (evL f d)
        (ThetaVal.omegaMul (ThetaShift.th d c (evL f c))))
    && ltC g c (evL f c)

/-- `g ≤ f` pointwise on the union of the supports (A4 Def 3.4.1). -/
def leL (g f : List (ι × α)) : Bool :=
  g.all fun p => decide (p.2 ≤ evL f p.1)

theorem hbL_of_le {g : List (ι × α)} {b : ι} (a : α) (h : sTop g ≤ b) : hbL g b a = g := by
  unfold hbL
  rw [if_neg (not_lt.2 h)]

theorem hbL_val (g : List (ι × α)) {b : ι} (a : α) (h : b < sTop g) :
    ∃ v, hbL g b a = trLt b g ++ [(b, v)] := by
  unfold hbL
  rw [if_pos h]
  exact ⟨_, rfl⟩

theorem trLt_hbL {g : List (ι × α)} {b : ι} (a : α) (h : b < sTop g) :
    trLt b (hbL g b a) = trLt b g := by
  obtain ⟨v, hv⟩ := hbL_val g a h
  rw [hv]
  unfold trLt
  rw [List.filter_append, List.filter_filter]
  simp

theorem Srt_hbL {g : List (ι × α)} (hg : Srt g) {b : ι} (a : α) : Srt (hbL g b a) := by
  by_cases h : b < sTop g
  · obtain ⟨v, hv⟩ := hbL_val g a h
    rw [hv, Srt, List.pairwise_append]
    refine ⟨List.Pairwise.sublist List.filter_sublist hg, by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst hy
    simpa [trLt] using (List.mem_filter.1 hx).2
  · rw [hbL_of_le a (not_lt.1 h)]
    exact hg

end Special

end FinFun

end OrdinalAnalysis.Frontier
