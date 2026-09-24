/-
  Fundamental sequences for the Veblen normal form below `Γ₀`.

  For every notation `x : Gamma0Note` and `n : ℕ` we define `fundSeq x n : Gamma0Note`, by
  structural recursion on the underlying `VNote`, following the classical assignment for the
  Veblen normal form. Writing `x[n]` for `fundSeq x n`:

  * `(φ_a(b)·k + c)[n] = φ_a(b)·k + c[n]` when `c ≠ 0`;
  * `(φ_a(b)·k)[n] = φ_a(b)·(k-1) + φ_a(b)[n]` when `k > 1`;
  * for a single term `φ_a(b)`:
    - `φ_0(0)[n] = 0` (the value is `1`);
    - `b` a limit: `φ_a(b)[n] = φ_a(b[n])`;
    - `b = b' + 1`, `a = 0`: `φ_0(b'+1)[n] = ω^{b'}·n`;
    - `b = b' + 1`, `a = a' + 1`: `φ_a(b)[n] = φ_{a'}^n(φ_a(b') + 1)`;
    - `b = b' + 1`, `a` a limit: `φ_a(b)[n] = φ_{a[n]}(φ_a(b') + 1)`;
    - `b = 0`, `a = a' + 1`: `φ_a(0)[n] = φ_{a'}^n(0)`;
    - `b = 0`, `a` a limit: `φ_a(0)[n] = φ_{a[n]}(0)`.

  At a successor notation the sequence is constantly the predecessor, so `x[n] < x` holds for
  every `x ≠ 0`. The main results are:

  * `Gamma0Note.fundSeq_lt`: `x[n] < x` for `x ≠ 0`;
  * `Gamma0Note.lt_repr_fundSeq`: at a limit `x`, the values `repr (x[n])` are cofinal in the
    ordinal `repr x` (every ordinal below `repr x`, not only every denoted one, is exceeded);
  * `Gamma0Note.exists_lt_fundSeq_of_lt`: the same for notations;
  * `Gamma0Note.monotone_fundSeq`: `n ↦ x[n]` is monotone;
  * the Veblen covers at a limit height or a limit level: `succCover_limit`,
    `limitCover_succ`, `limitCover_limit`.

  The limit-level successor-height cover rests on the ordinal fact
  `lt_veblen_add_one_iff_of_isSuccLimit`: for a limit `o`,
  `φ_o(c + 1) = sup_{γ < o} φ_γ(φ_o(c) + 1)`, proved here from
  `Ordinal.derivFamily_add_one` and `Ordinal.lt_nfpFamily_iff`; it is a general fact about
  `Ordinal.veblen` and belongs next to `Ordinal.veblen_of_ne_zero` in mathlib.
-/
import OrdinalAnalysis.Ordinal.Veblen.VeblenCover

set_option autoImplicit false

namespace OrdinalAnalysis

open Ordinal

/-! ### Ordinal preliminaries -/

/-- `φ_a(b) = 1` exactly when `a = b = 0`. -/
theorem veblen_eq_one_iff {a b : Ordinal} : veblen a b = 1 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have ha : a = 0 := by
      by_contra ha
      have h1 : veblen 0 0 < veblen a 0 :=
        veblen_zero_strictMono (pos_iff_ne_zero.2 ha)
      have h2 : veblen a 0 ≤ veblen a b := (veblen_right_strictMono a).monotone bot_le
      rw [veblen_zero_apply, opow_zero] at h1
      exact absurd (h ▸ h1.trans_le h2) (lt_irrefl _)
    subst ha
    refine ⟨rfl, ?_⟩
    by_contra hb
    have h1 : (ω : Ordinal) ^ (0 : Ordinal) < ω ^ b :=
      (opow_lt_opow_iff_right one_lt_omega0).2 (pos_iff_ne_zero.2 hb)
    rw [opow_zero, ← veblen_zero_apply, h] at h1
    exact lt_irrefl _ h1
  · rintro ⟨rfl, rfl⟩
    rw [veblen_zero_apply, opow_zero]

/-- If `b' < b` then `φ_a(b') + 1 < φ_a(b)`. -/
theorem veblen_add_one_lt_veblen {a b' b : Ordinal} (h : b' < b) :
    veblen a b' + 1 < veblen a b := by
  have h1 : veblen a b ≠ 1 := fun h1 =>
    absurd (veblen_eq_one_iff.1 h1).2 (pos_iff_ne_zero.1 (bot_le.trans_lt h))
  have hone : (1 : Ordinal) < veblen a b :=
    lt_of_le_of_ne (Order.one_le_iff_ne_zero.2 veblen_pos.ne') (Ne.symm h1)
  exact isPrincipal_add_veblen a b ((veblen_right_strictMono a) h) hone

/-- A successor ordinal `c + 1` is never a fixed point of any `φ_γ`. -/
theorem add_one_lt_veblen (γ c : Ordinal) : c + 1 < veblen γ (c + 1) := by
  refine (right_le_veblen γ (c + 1)).lt_of_ne fun heq => ?_
  rcases veblen_eq_one_or_isSuccLimit γ (c + 1) with h1 | h1
  · have h2 := (veblen_eq_one_iff.1 h1).2
    simp at h2
  · rw [← heq, ← Order.succ_eq_add_one] at h1
    exact Order.not_isSuccLimit_succ c h1

/-- Finite iterates of `φ_{a'}` from a point below a fixed point of `φ_{a'}` stay below it. -/
theorem iterate_veblen_lt {a' F z : Ordinal} (hF : veblen a' F = F) (hz : z < F) :
    ∀ n : ℕ, (veblen a')^[n] z < F
  | 0 => hz
  | n + 1 => by
    rw [Function.iterate_succ_apply', ← hF]
    exact (veblen_right_strictMono a') (iterate_veblen_lt hF hz n)

/-- **Limit-level Veblen at a successor argument.** For a limit `o`, every ordinal below
`φ_o(c + 1)` lies below `φ_γ(φ_o(c) + 1)` for some `γ < o`; that is,
`φ_o(c + 1) = sup_{γ < o} φ_γ(φ_o(c) + 1)`. -/
theorem lt_veblen_add_one_iff_of_isSuccLimit {o c x : Ordinal} (ho : Order.IsSuccLimit o) :
    x < veblen o (c + 1) ↔ ∃ γ < o, x < veblen γ (veblen o c + 1) := by
  constructor
  · intro hx
    have h0 : o ≠ 0 := ho.pos.ne'
    have e : veblen o (c + 1) =
        nfpFamily (fun i : Set.Iio o => veblen i.1) (veblen o c + 1) := by
      rw [veblen_of_ne_zero h0, derivFamily_add_one]
    rw [e, lt_nfpFamily_iff] at hx
    obtain ⟨l, hl⟩ := hx
    set y := veblen o c + 1 with hy
    have key : ∀ l : List (Set.Iio o), ∃ γ < o,
        List.foldr (fun i : Set.Iio o => veblen i.1) y l < veblen γ y := by
      intro l
      induction l with
      | nil => exact ⟨0, ho.pos, by simpa [hy] using add_one_lt_veblen 0 (veblen o c)⟩
      | cons i l ih =>
        obtain ⟨γ, hγo, hγ⟩ := ih
        have hi : i.1 + 1 < o := by
          have := ho.succ_lt i.2
          rwa [Order.succ_eq_add_one] at this
        refine ⟨max γ (i.1 + 1), max_lt hγo hi, ?_⟩
        have hlt : i.1 < max γ (i.1 + 1) := (lt_add_one i.1).trans_le (le_max_right _ _)
        have h1 : List.foldr (fun i : Set.Iio o => veblen i.1) y l < veblen (max γ (i.1 + 1)) y :=
          hγ.trans_le (veblen_left_monotone y (le_max_left _ _))
        rw [List.foldr_cons, ← veblen_veblen_of_lt hlt y]
        exact (veblen_right_strictMono i.1) h1
    obtain ⟨γ, hγo, hγ⟩ := key l
    exact ⟨γ, hγo, hl.trans hγ⟩
  · rintro ⟨γ, hγo, hx⟩
    refine hx.trans ?_
    rw [veblen_lt_veblen_iff]
    exact Or.inr (Or.inl ⟨hγo, veblen_add_one_lt_veblen (lt_add_one c)⟩)

/-- Cofinality transfers across a left summand: if `f` is cofinal in `c`, then `P + f` is
cofinal in `P + c`. -/
theorem exists_lt_add_of_cofinal {P c : Ordinal} {f : ℕ → Ordinal}
    (hcof : ∀ d < c, ∃ n, d < f n) : ∀ o < P + c, ∃ n, o < P + f n := by
  intro o ho
  by_cases hP : o < P
  · exact ⟨0, hP.trans_le le_self_add⟩
  · rw [not_lt] at hP
    have hd : o - P < c := by
      rw [← add_lt_add_iff_left P, Ordinal.add_sub_cancel_of_le hP]
      exact ho
    obtain ⟨n, hn⟩ := hcof _ hd
    refine ⟨n, ?_⟩
    rw [← Ordinal.add_sub_cancel_of_le hP]
    exact (add_lt_add_iff_left P).2 hn

namespace VNote

/-! ### Syntactic predecessor -/

/-- The predecessor of a successor notation, read off the syntax: `some p` when the notation
denotes `repr p + 1`, and `none` for `0` and for limits. -/
def pred : VNote → Option VNote
  | 0 => none
  | vadd a b k c =>
    if c = 0 then
      (if a = 0 ∧ b = 0 then some (if k = 1 then 0 else vadd 0 0 (k - 1) 0) else none)
    else (pred c).map (fun p => vadd a b k p)

theorem pred_spec : ∀ {x : VNote}, NF x →
    (∀ p, pred x = some p → NF p ∧ repr p + 1 = repr x) ∧
      (pred x = none → x = 0 ∨ Order.IsSuccLimit (repr x)) := by
  intro x
  induction x with
  | zero =>
    intro _
    exact ⟨fun p hp => by simp [pred] at hp, fun _ => Or.inl rfl⟩
  | vadd a b k c _ _ ihc =>
    intro hx
    by_cases hc : c = 0
    · subst hc
      by_cases hab : a = 0 ∧ b = 0
      · obtain ⟨rfl, rfl⟩ := hab
        have hpred : pred (vadd 0 0 k 0) = some (if k = 1 then 0 else vadd 0 0 (k - 1) 0) := by
          simp [pred]
        refine ⟨fun p hp => ?_, fun h => by rw [hpred] at h; exact absurd h (by simp)⟩
        rw [hpred, Option.some_inj] at hp
        subst hp
        have hone : veblen (repr (0 : VNote)) (repr (0 : VNote)) = 1 := by
          rw [repr_zero, veblen_zero_apply, opow_zero]
        by_cases hk : k = 1
        · subst hk
          simp only [if_true]
          refine ⟨NF.zero, ?_⟩
          rw [repr_vadd, hone]
          simp
        · simp only [hk, if_false]
          have hk1' : 1 < (k : ℕ) := by
            rcases Nat.lt_or_ge 1 (k : ℕ) with h | h
            · exact h
            · exact absurd (PNat.coe_eq_one_iff.1 (le_antisymm h k.pos)) hk
          have hk1 : 1 < k := hk1'
          refine ⟨NF.vadd_zero _ NF.zero NF.zero (by rw [hone]; simp), ?_⟩
          rw [repr_vadd, repr_vadd, hone, PNat.sub_coe, if_pos hk1, PNat.one_coe]
          have hnat : ((k : ℕ) - 1) + 1 = (k : ℕ) := by omega
          simp only [one_mul, repr_zero, add_zero]
          exact_mod_cast hnat
      · have hpred : pred (vadd a b k 0) = none := by simp [pred, hab]
        refine ⟨fun p hp => by rw [hpred] at hp; exact absurd hp (by simp), fun _ => ?_⟩
        right
        rw [repr_vadd, repr_zero, add_zero]
        rcases veblen_eq_one_or_isSuccLimit (repr a) (repr b) with h1 | h1
        · obtain ⟨ha, hb⟩ := veblen_eq_one_iff.1 h1
          exact absurd ⟨repr_eq_zero_iff.1 ha, repr_eq_zero_iff.1 hb⟩ hab
        · exact isSuccLimit_mul_natCast h1 (k : ℕ) k.property
    · have hpred : pred (vadd a b k c) = (pred c).map (fun p => vadd a b k p) := by
        simp [pred, hc]
      obtain ⟨ih1, ih2⟩ := ihc hx.tail
      refine ⟨fun p hp => ?_, fun h => ?_⟩
      · rw [hpred, Option.map_eq_some_iff] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        obtain ⟨hqnf, hqr⟩ := ih1 q hq
        have hqc : repr q < repr c := hqr ▸ lt_add_one (repr q)
        refine ⟨NF.vadd hx.fst hx.snd hqnf hx.snd_lt (hqc.trans hx.tail_lt), ?_⟩
        rw [repr_vadd, repr_vadd, add_assoc, hqr]
      · rw [hpred, Option.map_eq_none_iff] at h
        rcases ih2 h with h0 | hlim
        · exact absurd h0 hc
        · right
          rw [repr_vadd]
          exact isSuccLimit_add _ hlim

/-! ### Auxiliary constructors -/

/-- Finite iteration of the total Veblen constructor `veblenNote a'`. -/
def iterV (a' : VNote) (n : ℕ) (z : VNote) : VNote :=
  (veblenNote a')^[n] z

theorem nf_and_repr_iterV {a' : VNote} (ha' : NF a') :
    ∀ (n : ℕ) {z : VNote}, NF z →
      NF (iterV a' n z) ∧ repr (iterV a' n z) = (veblen (repr a'))^[n] (repr z)
  | 0, z, hz => ⟨hz, rfl⟩
  | n + 1, z, hz => by
    obtain ⟨h1, h2⟩ := nf_and_repr_iterV ha' n hz
    have e : iterV a' (n + 1) z = veblenNote a' (iterV a' n z) :=
      Function.iterate_succ_apply' _ n z
    rw [e, Function.iterate_succ_apply', ← h2]
    exact nf_and_repr_veblenNote ha' h1

/-- The `n`-fold multiple of a single Veblen term. -/
def smul : VNote → ℕ → VNote
  | vadd p q _ _, n + 1 => vadd p q (Nat.succPNat n) 0
  | _, _ => 0

/-- `veblenNote a b` is always a single Veblen term with multiplicity `1` and no tail. -/
theorem veblenNote_eq_single (a b : VNote) : ∃ p q, veblenNote a b = vadd p q 1 0 := by
  cases b with
  | zero => exact ⟨a, 0, rfl⟩
  | vadd b₁ b₂ n c =>
    by_cases htest : n = 1 ∧ c = 0 ∧ cmp a b₁ = Ordering.lt
    · obtain ⟨hn, hc, hcmp⟩ := htest
      subst hn; subst hc
      refine ⟨b₁, b₂, ?_⟩
      rw [veblenNote, if_pos ⟨rfl, rfl, hcmp⟩]
    · exact ⟨a, vadd b₁ b₂ n c, by rw [veblenNote, if_neg htest]⟩

theorem nf_and_repr_smul_veblenNote {a b : VNote} (ha : NF a) (hb : NF b) (n : ℕ) :
    NF (smul (veblenNote a b) n) ∧
      repr (smul (veblenNote a b) n) = veblen (repr a) (repr b) * n := by
  obtain ⟨hnf, hr⟩ := nf_and_repr_veblenNote ha hb
  obtain ⟨p, q, e⟩ := veblenNote_eq_single a b
  rw [e] at hnf hr ⊢
  rw [repr_vadd_one_zero] at hr
  cases n with
  | zero => exact ⟨NF.zero, by simp [smul]⟩
  | succ n =>
    refine ⟨NF.vadd_zero _ hnf.fst hnf.snd hnf.snd_lt, ?_⟩
    simp [smul, hr]

theorem nf_and_repr_nadd_one {x : VNote} (hx : NF x) :
    NF (nadd x 1) ∧ repr (nadd x 1) = repr x + 1 :=
  ⟨nf_nadd hx nf_one, Gamma0Note.repr_nadd_one ⟨x, hx⟩⟩

/-! ### The fundamental sequence of a single Veblen term -/

/-- The fundamental sequence of the single term `φ_a(b)`, given the fundamental sequences
`fa` of `a` and `fb` of `b`. -/
def termFS (a b : VNote) (fa fb : ℕ → VNote) (n : ℕ) : VNote :=
  match pred b with
  | some b' =>
    if a = 0 then smul (veblenNote 0 b') n
    else
      match pred a with
      | some a' => iterV a' n (nadd (veblenNote a b') 1)
      | none => veblenNote (fa n) (nadd (veblenNote a b') 1)
  | none =>
    if b = 0 then
      if a = 0 then 0
      else
        match pred a with
        | some a' => iterV a' n 0
        | none => veblenNote (fa n) 0
    else veblenNote a (fb n)

/-- The properties of a fundamental-sequence candidate `f` for a notation `x`. -/
structure IsFS (x : VNote) (f : ℕ → VNote) : Prop where
  nf : ∀ n, NF (f n)
  lt : x ≠ 0 → ∀ n, repr (f n) < repr x
  cof : Order.IsSuccLimit (repr x) → ∀ o < repr x, ∃ n, o < repr (f n)
  mono : Monotone fun n => repr (f n)

section termFS

variable {a b : VNote} {fa fb : ℕ → VNote}

theorem termFS_spec (ha : NF a) (hb : NF b) (hab : repr b < veblen (repr a) (repr b))
    (hfa : IsFS a fa) (hfb : IsFS b fb) :
    (∀ n, NF (termFS a b fa fb n) ∧ repr (termFS a b fa fb n) < veblen (repr a) (repr b)) ∧
      (¬ (a = 0 ∧ b = 0) → ∀ o < veblen (repr a) (repr b),
        ∃ n, o < repr (termFS a b fa fb n)) ∧
      Monotone fun n => repr (termFS a b fa fb n) := by
  obtain ⟨hpb1, hpb2⟩ := pred_spec hb
  rcases hpbe : pred b with _ | b'
  · -- `b` is `0` or a limit
    by_cases hb0 : b = 0
    · subst hb0
      by_cases ha0 : a = 0
      · subst ha0
        have e : ∀ n, termFS 0 0 fa fb n = 0 := fun n => by simp [termFS, hpbe]
        simp only [e]
        exact ⟨fun _ => ⟨NF.zero, veblen_pos⟩, fun h => absurd (by simp) h,
          fun _ _ _ => le_rfl⟩
      · obtain ⟨hpa1, hpa2⟩ := pred_spec ha
        rcases hpae : pred a with _ | a'
        · -- `a` a limit
          have hal : Order.IsSuccLimit (repr a) := (hpa2 hpae).resolve_left ha0
          have e : ∀ n, termFS a 0 fa fb n = veblenNote (fa n) 0 := fun n => by
            simp [termFS, hpbe, hpae, ha0]
          simp only [e]
          have hr : ∀ n, repr (veblenNote (fa n) 0) = veblen (repr (fa n)) 0 := fun n => by
            rw [repr_veblenNote (hfa.nf n) NF.zero, repr_zero]
          simp only [hr, repr_zero]
          refine ⟨fun n => ⟨nf_veblenNote (hfa.nf n) NF.zero,
            veblen_zero_strictMono (hfa.lt ha0 n)⟩, fun _ o ho => ?_, fun n m hnm => ?_⟩
          · obtain ⟨γ, hγ, hoγ⟩ := (isNormal_veblen_zero.lt_iff_exists_lt hal).1 ho
            obtain ⟨n, hn⟩ := hfa.cof hal γ hγ
            exact ⟨n, hoγ.trans (veblen_zero_strictMono hn)⟩
          · exact veblen_left_monotone 0 (hfa.mono hnm)
        · -- `a = a' + 1`
          obtain ⟨ha'nf, ha'r⟩ := hpa1 a' hpae
          have e : ∀ n, termFS a 0 fa fb n = iterV a' n 0 := fun n => by
            simp [termFS, hpbe, hpae, ha0]
          simp only [e]
          have hr : ∀ n, repr (iterV a' n 0) = (veblen (repr a'))^[n] 0 := fun n =>
            (nf_and_repr_iterV ha'nf n NF.zero).2
          simp only [hr, repr_zero]
          have hF : veblen (repr a') (veblen (repr a) 0) = veblen (repr a) 0 :=
            veblen_veblen_of_lt (ha'r ▸ lt_add_one (repr a')) 0
          refine ⟨fun n => ⟨(nf_and_repr_iterV ha'nf n NF.zero).1,
            iterate_veblen_lt hF veblen_pos n⟩, fun _ o ho => ?_, ?_⟩
          · rw [← ha'r, veblen_add_one, deriv_zero_right, lt_nfp_iff] at ho
            exact ho
          · apply monotone_nat_of_le_succ
            intro n
            rw [Function.iterate_succ_apply']
            exact right_le_veblen _ _
    · -- `b` a limit
      have hbl : Order.IsSuccLimit (repr b) := (hpb2 hpbe).resolve_left hb0
      have e : ∀ n, termFS a b fa fb n = veblenNote a (fb n) := fun n => by
        simp [termFS, hpbe, hb0]
      simp only [e]
      have hr : ∀ n, repr (veblenNote a (fb n)) = veblen (repr a) (repr (fb n)) := fun n =>
        repr_veblenNote ha (hfb.nf n)
      simp only [hr]
      refine ⟨fun n => ⟨nf_veblenNote ha (hfb.nf n),
        (veblen_right_strictMono _) (hfb.lt hb0 n)⟩, fun _ o ho => ?_, fun n m hnm => ?_⟩
      · obtain ⟨γ, hγ, hoγ⟩ := ((isNormal_veblen (repr a)).lt_iff_exists_lt hbl).1 ho
        obtain ⟨n, hn⟩ := hfb.cof hbl γ hγ
        exact ⟨n, hoγ.trans ((veblen_right_strictMono _) hn)⟩
      · exact (veblen_right_strictMono _).monotone (hfb.mono hnm)
  · -- `b = b' + 1`
    obtain ⟨hb'nf, hb'r⟩ := hpb1 b' hpbe
    have hb'b : repr b' < repr b := hb'r ▸ lt_add_one (repr b')
    by_cases ha0 : a = 0
    · subst ha0
      have e : ∀ n, termFS 0 b fa fb n = smul (veblenNote 0 b') n := fun n => by
        simp [termFS, hpbe]
      simp only [e]
      have hr : ∀ n : ℕ, repr (smul (veblenNote 0 b') n) = ω ^ repr b' * n := fun n => by
        rw [(nf_and_repr_smul_veblenNote NF.zero hb'nf n).2, repr_zero, veblen_zero_apply]
      simp only [hr]
      have hV : veblen (repr (0 : VNote)) (repr b) = ω ^ repr b' * ω := by
        rw [repr_zero, veblen_zero_apply, ← hb'r, opow_add, opow_one]
      rw [hV]
      have hpos : (0 : Ordinal) < ω ^ repr b' := opow_pos _ omega0_pos
      refine ⟨fun n => ⟨(nf_and_repr_smul_veblenNote NF.zero hb'nf n).1, ?_⟩,
        fun _ o ho => ?_, fun n m hnm => ?_⟩
      · exact (mul_lt_mul_iff_right₀ hpos).2 (natCast_lt_omega0 n)
      · obtain ⟨c', hc', hoc'⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 ho
        obtain ⟨n, rfl⟩ := lt_omega0.1 hc'
        exact ⟨n, hoc'⟩
      · exact mul_le_mul_right (by exact_mod_cast hnm) _
    · obtain ⟨hpa1, hpa2⟩ := pred_spec ha
      have hz := nf_and_repr_nadd_one (nf_veblenNote ha hb'nf)
      rw [repr_veblenNote ha hb'nf] at hz
      have hzlt : veblen (repr a) (repr b') + 1 < veblen (repr a) (repr b) :=
        veblen_add_one_lt_veblen hb'b
      rcases hpae : pred a with _ | a'
      · -- `a` a limit
        have hal : Order.IsSuccLimit (repr a) := (hpa2 hpae).resolve_left ha0
        have e : ∀ n, termFS a b fa fb n =
            veblenNote (fa n) (nadd (veblenNote a b') 1) := fun n => by
          simp [termFS, hpbe, hpae, ha0]
        simp only [e]
        have hr : ∀ n, repr (veblenNote (fa n) (nadd (veblenNote a b') 1)) =
            veblen (repr (fa n)) (veblen (repr a) (repr b') + 1) := fun n => by
          rw [repr_veblenNote (hfa.nf n) hz.1, hz.2]
        simp only [hr]
        refine ⟨fun n => ⟨nf_veblenNote (hfa.nf n) hz.1, ?_⟩, fun _ o ho => ?_,
          fun n m hnm => ?_⟩
        · rw [veblen_lt_veblen_iff]
          exact Or.inr (Or.inl ⟨hfa.lt ha0 n, hzlt⟩)
        · rw [← hb'r, lt_veblen_add_one_iff_of_isSuccLimit hal] at ho
          obtain ⟨γ, hγ, hoγ⟩ := ho
          obtain ⟨n, hn⟩ := hfa.cof hal γ hγ
          exact ⟨n, hoγ.trans_le (veblen_left_monotone _ hn.le)⟩
        · exact veblen_left_monotone _ (hfa.mono hnm)
      · -- `a = a' + 1`
        obtain ⟨ha'nf, ha'r⟩ := hpa1 a' hpae
        have e : ∀ n, termFS a b fa fb n = iterV a' n (nadd (veblenNote a b') 1) :=
          fun n => by simp [termFS, hpbe, hpae, ha0]
        simp only [e]
        have hr : ∀ n, repr (iterV a' n (nadd (veblenNote a b') 1)) =
            (veblen (repr a'))^[n] (veblen (repr a) (repr b') + 1) := fun n => by
          rw [(nf_and_repr_iterV ha'nf n hz.1).2, hz.2]
        simp only [hr]
        have hF : veblen (repr a') (veblen (repr a) (repr b)) = veblen (repr a) (repr b) :=
          veblen_veblen_of_lt (ha'r ▸ lt_add_one (repr a')) _
        refine ⟨fun n => ⟨(nf_and_repr_iterV ha'nf n hz.1).1,
          iterate_veblen_lt hF hzlt n⟩, fun _ o ho => ?_, ?_⟩
        · rw [← hb'r, ← ha'r, veblen_add_one, deriv_add_one, ← veblen_add_one,
            lt_nfp_iff] at ho
          rw [← ha'r]
          exact ho
        · apply monotone_nat_of_le_succ
          intro n
          rw [Function.iterate_succ_apply']
          exact right_le_veblen _ _

end termFS

/-! ### The fundamental sequence -/

/-- The fundamental sequence of a Veblen notation (see the module docstring). At a
successor notation it is constantly the predecessor. -/
def fundSeq : VNote → ℕ → VNote
  | 0 => fun _ => 0
  | vadd a b k c => fun n =>
    if c = 0 then
      (if k = 1 then termFS a b (fundSeq a) (fundSeq b) n
        else vadd a b (k - 1) (termFS a b (fundSeq a) (fundSeq b) n))
    else vadd a b k (fundSeq c n)

theorem isFS_fundSeq : ∀ {x : VNote}, NF x → IsFS x (fundSeq x) := by
  intro x
  induction x with
  | zero =>
    intro _
    refine ⟨fun _ => NF.zero, fun h => absurd rfl h, fun h => ?_, fun _ _ _ => le_rfl⟩
    exact absurd h Ordinal.not_isSuccLimit_zero
  | vadd a b k c iha ihb ihc =>
    intro hx
    have hV := hx.snd_lt
    obtain ⟨hT, hTcof, hTmono⟩ :=
      termFS_spec hx.fst hx.snd hV (iha hx.fst) (ihb hx.snd)
    by_cases hc : c = 0
    · subst hc
      by_cases hk : k = 1
      · subst hk
        have e : ∀ n, fundSeq (vadd a b 1 0) n = termFS a b (fundSeq a) (fundSeq b) n :=
          fun n => by simp [fundSeq]
        have hr : repr (vadd a b 1 0) = veblen (repr a) (repr b) := repr_vadd_one_zero a b
        refine ⟨fun n => e n ▸ (hT n).1, fun _ n => e n ▸ hr ▸ (hT n).2, fun hl => ?_, ?_⟩
        · rw [hr] at hl ⊢
          have hab : ¬ (a = 0 ∧ b = 0) := by
            rintro ⟨rfl, rfl⟩
            rw [repr_zero, veblen_zero_apply, opow_zero] at hl
            exact absurd (one_lt_of_isSuccLimit hl) (lt_irrefl 1)
          intro o ho
          obtain ⟨n, hn⟩ := hTcof hab o ho
          exact ⟨n, e n ▸ hn⟩
        · simp only [e]; exact hTmono
      · have hk1' : 1 < (k : ℕ) := by
          rcases Nat.lt_or_ge 1 (k : ℕ) with h | h
          · exact h
          · exact absurd (PNat.coe_eq_one_iff.1 (le_antisymm h k.pos)) hk
        have hk1 : 1 < k := hk1'
        have hkc : (((k - 1 : ℕ+) : ℕ) : Ordinal) + 1 = ((k : ℕ) : Ordinal) := by
          rw [PNat.sub_coe, if_pos hk1, PNat.one_coe]
          have hnat : ((k : ℕ) - 1) + 1 = (k : ℕ) := by omega
          exact_mod_cast hnat
        have e : fundSeq (vadd a b k 0) =
            fun n => vadd a b (k - 1) (termFS a b (fundSeq a) (fundSeq b) n) := by
          funext n; simp [fundSeq, hk]
        rw [e]
        set V := veblen (repr a) (repr b) with hVdef
        have hsplit : V * ((k : ℕ) : Ordinal) = V * (((k - 1 : ℕ+) : ℕ) : Ordinal) + V := by
          rw [← hkc, mul_add_one]
        refine ⟨fun n => NF.vadd hx.fst hx.snd (hT n).1 hV (hT n).2, fun _ n => ?_,
          fun hl => ?_, fun n m hnm => ?_⟩
        · simp only [repr_vadd, repr_zero, add_zero]
          rw [hsplit]
          exact (add_lt_add_iff_left _).2 (hT n).2
        · simp only [repr_vadd, repr_zero, add_zero] at hl ⊢
          have hab : ¬ (a = 0 ∧ b = 0) := by
            rintro ⟨rfl, rfl⟩
            rw [repr_zero, veblen_zero_apply, opow_zero, one_mul] at hl
            exact absurd (natCast_lt_of_isSuccLimit hl (k : ℕ)) (lt_irrefl _)
          rw [hsplit]
          exact exists_lt_add_of_cofinal (hTcof hab)
        · simp only [repr_vadd]
          exact (add_le_add_iff_left _).2 (hTmono hnm)
    · have e : fundSeq (vadd a b k c) = fun n => vadd a b k (fundSeq c n) := by
        funext n; simp [fundSeq, hc]
      rw [e]
      have hC := ihc hx.tail
      refine ⟨fun n => NF.vadd hx.fst hx.snd (hC.nf n) hV ((hC.lt hc n).trans hx.tail_lt),
        fun _ n => ?_, fun hl => ?_, fun n m hnm => ?_⟩
      · simp only [repr_vadd]
        exact (add_lt_add_iff_left _).2 (hC.lt hc n)
      · simp only [repr_vadd] at hl ⊢
        have hcl : Order.IsSuccLimit (repr c) := by
          rcases zero_or_exists_pred_or_isSuccLimit c hx.tail with h0 | ⟨p, _, hp⟩ | h
          · exact absurd h0 hc
          · rw [← hp, ← add_assoc, ← Order.succ_eq_add_one] at hl
            exact absurd hl (Order.not_isSuccLimit_succ _)
          · exact h
        exact exists_lt_add_of_cofinal (hC.cof hcl)
      · simp only [repr_vadd]
        exact (add_le_add_iff_left _).2 (hC.mono hnm)

end VNote

namespace Gamma0Note

/-! ### Fundamental sequences on `Gamma0Note` -/

/-- The fundamental sequence of a Veblen normal form: `fundSeq x n` is the `n`-th element
`x[n]`. At a successor it is constantly the predecessor; at `0` it is `0`. -/
def fundSeq (x : Gamma0Note) (n : ℕ) : Gamma0Note :=
  ⟨VNote.fundSeq x.1 n, (VNote.isFS_fundSeq x.2).nf n⟩

theorem repr_fundSeq (x : Gamma0Note) (n : ℕ) :
    repr (fundSeq x n) = VNote.repr (VNote.fundSeq x.1 n) := rfl

theorem ne_zero_of_isSuccLimit {x : Gamma0Note} (hx : Order.IsSuccLimit (repr x)) : x ≠ 0 := by
  rintro rfl
  rw [repr_zero] at hx
  exact Ordinal.not_isSuccLimit_zero hx

/-- **Descent.** Every element of the fundamental sequence of a nonzero notation lies below
it. -/
theorem fundSeq_lt {x : Gamma0Note} (hx : x ≠ 0) (n : ℕ) : fundSeq x n < x := by
  have hx' : x.1 ≠ 0 := fun h => hx (Subtype.ext h)
  exact (VNote.isFS_fundSeq x.2).lt hx' n

/-- **Monotonicity** of the fundamental sequence in its index. -/
theorem monotone_fundSeq (x : Gamma0Note) : Monotone (fundSeq x) := fun _ _ h =>
  (VNote.isFS_fundSeq x.2).mono h

/-- **Cofinality, ordinal form.** At a limit notation `x`, every ordinal below `repr x` —
denoted or not — lies below some `repr (x[n])`. -/
theorem lt_repr_fundSeq {x : Gamma0Note} (hx : Order.IsSuccLimit (repr x)) {o : Ordinal}
    (ho : o < repr x) : ∃ n, o < repr (fundSeq x n) :=
  (VNote.isFS_fundSeq x.2).cof hx o ho

/-- **Cofinality.** At a limit notation `x`, every notation below `x` lies below some
`x[n]`. -/
theorem exists_lt_fundSeq_of_lt {x y : Gamma0Note} (hx : Order.IsSuccLimit (repr x))
    (hy : y < x) : ∃ n, y < fundSeq x n :=
  lt_repr_fundSeq hx (lt_def.1 hy)

/-- At a limit notation the values of the fundamental sequence have supremum `repr x`. -/
theorem iSup_repr_fundSeq {x : Gamma0Note} (hx : Order.IsSuccLimit (repr x)) :
    ⨆ n, repr (fundSeq x n) = repr x := by
  have hne : x ≠ 0 := ne_zero_of_isSuccLimit hx
  refine le_antisymm (Ordinal.iSup_le fun n => (fundSeq_lt hne n).le) ?_
  refine le_of_forall_lt fun o ho => ?_
  obtain ⟨n, hn⟩ := lt_repr_fundSeq hx ho
  exact hn.trans_le (Ordinal.le_iSup _ n)

/-! ### Veblen covers at a limit height or a limit level -/

/-- **Cover at a limit height, any level.** If `h` is a limit and `x < φ_a(h)`, then
`x < φ_a(h[n])` for some `n`. -/
theorem exists_lt_veblenNote_fundSeq {a h x : Gamma0Note} (hh : Order.IsSuccLimit (repr h))
    (hx : x < veblenNote a h) : ∃ n, x < veblenNote a (fundSeq h n) := by
  rw [lt_def, repr_veblenNote] at hx
  obtain ⟨g', hg', hxg'⟩ := ((isNormal_veblen (repr a)).lt_iff_exists_lt hh).1 hx
  obtain ⟨n, hn⟩ := lt_repr_fundSeq hh hg'
  refine ⟨n, ?_⟩
  rw [lt_def, repr_veblenNote]
  exact hxg'.trans ((veblen_right_strictMono _) hn)

/-- **Successor-level cover, `h` a limit.** Every `x < φ_{β ⊕ 1}(h)` lies below
`φ_{β ⊕ 1}(g)` for some notation `g < h`. -/
theorem succCover_limit {β h x : Gamma0Note} (hh : Order.IsSuccLimit (repr h))
    (hx : x < veblenNote (nadd β 1) h) : ∃ g : Gamma0Note, g < h ∧ x < veblenNote (nadd β 1) g := by
  have hne : h ≠ 0 := ne_zero_of_isSuccLimit hh
  obtain ⟨n, hn⟩ := exists_lt_veblenNote_fundSeq hh hx
  exact ⟨fundSeq h n, fundSeq_lt hne n, hn⟩

/-- **Limit-level cover, `h` a limit.** Every `x < φ_a(h)` lies below `φ_a(g)` for some
notation `g < h`. The limit hypothesis on `a` is not needed: the fact holds at every level. -/
theorem limitCover_limit {a h x : Gamma0Note} (hh : Order.IsSuccLimit (repr h))
    (hx : x < veblenNote a h) : ∃ g : Gamma0Note, g < h ∧ x < veblenNote a g := by
  have hne : h ≠ 0 := ne_zero_of_isSuccLimit hh
  obtain ⟨n, hn⟩ := exists_lt_veblenNote_fundSeq hh hx
  exact ⟨fundSeq h n, fundSeq_lt hne n, hn⟩

/-- **Limit-level cover, `h` a successor, sequence form.** For a limit `a`, every
`x < φ_a(g ⊕ 1)` lies below `φ_{a[n]}(φ_a(g) ⊕ 1)` for some `n`. -/
theorem exists_lt_veblenNote_fundSeq_succ {a g x : Gamma0Note}
    (ha : Order.IsSuccLimit (repr a)) (hx : x < veblenNote a (nadd g 1)) :
    ∃ n, x < veblenNote (fundSeq a n) (nadd (veblenNote a g) 1) := by
  rw [lt_def, repr_veblenNote, repr_nadd_one, lt_veblen_add_one_iff_of_isSuccLimit ha] at hx
  obtain ⟨γ, hγ, hxγ⟩ := hx
  obtain ⟨n, hn⟩ := lt_repr_fundSeq ha hγ
  refine ⟨n, ?_⟩
  rw [lt_def, repr_veblenNote, repr_nadd_one, repr_veblenNote]
  exact hxγ.trans_le (veblen_left_monotone _ hn.le)

/-- **Limit-level cover, `h` a successor.** For a limit `a`, every `x < φ_a(g ⊕ 1)` lies
below `φ_{β''}(φ_a(g) ⊕ 1)` for some notation `β'' < a`. -/
theorem limitCover_succ {a g x : Gamma0Note} (ha : Order.IsSuccLimit (repr a))
    (hx : x < veblenNote a (nadd g 1)) :
    ∃ β'' : Gamma0Note, β'' < a ∧ x < veblenNote β'' (nadd (veblenNote a g) 1) := by
  have hne : a ≠ 0 := ne_zero_of_isSuccLimit ha
  obtain ⟨n, hn⟩ := exists_lt_veblenNote_fundSeq_succ ha hx
  exact ⟨fundSeq a n, fundSeq_lt hne n, hn⟩

end Gamma0Note

end OrdinalAnalysis
