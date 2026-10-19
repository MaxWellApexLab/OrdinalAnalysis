module

public import OrdinalAnalysis.KPi.SoundAux1

@[expose] public section

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.Sound

open LO LO.FirstOrder OrdinalAnalysis.KPi.RS

/-! ### Translation of Foundation Δ₀-formulas into RS-formulas -/

/-- the variable of a term. -/
def trTm {n k : ℕ} (bv : Fin n → Fin k) (fv : ℕ → Fin k) : Semiterm LAd ℕ n → Fin k
  | .bvar i => bv i
  | .fvar x => fv x
  | .func g _ => Empty.elim g

/-- the bound of a restricted quantifier (a term under the binder, never `#0`). -/
def trBd {n k : ℕ} (bv : Fin n → Fin k) (fv : ℕ → Fin k) : Semiterm LAd ℕ (n + 1) → Bd k
  | .bvar i => Fin.cases (Bd.lev 0) (fun j => Bd.var (bv j)) i
  | .fvar x => Bd.var (fv x)
  | .func g _ => Empty.elim g

/-- bound-variable map under a binder. -/
def bvExt {n k : ℕ} (bv : Fin n → Fin k) : Fin (n + 1) → Fin (k + 1) :=
  Fin.cons (Fin.last k) (fun j => (bv j).castSucc)

def trTrue (k : ℕ) : D0 k := D0.ball (Bd.lev 0) (D0.nmem (Fin.last k) (Fin.last k))
def trFalse (k : ℕ) : D0 k := D0.bex (Bd.lev 0) (D0.mem (Fin.last k) (Fin.last k))

/-- `tr fv bv φ`: the RS-formula of a Δ₀-formula `φ`; the free variable `&j` is the variable `fv j`,
the bound variable `#i` is `bv i`.  (Unrestricted quantifiers are sent to a junk value.) -/
def tr : {k n : ℕ} → (ℕ → Fin k) → (Fin n → Fin k) → Semiformula LAd ℕ n → D0 k
  | k, _, _, _, .verum => trTrue k
  | k, _, _, _, .falsum => trFalse k
  | _, _, fv, bv, .rel AdRel.mem v => D0.mem (trTm bv fv (v 0)) (trTm bv fv (v 1))
  | _, _, fv, bv, .rel AdRel.ad v => D0.ad (trTm bv fv (v 0))
  | _, _, fv, bv, .nrel AdRel.mem v => D0.nmem (trTm bv fv (v 0)) (trTm bv fv (v 1))
  | _, _, fv, bv, .nrel AdRel.ad v => D0.nad (trTm bv fv (v 0))
  | _, _, fv, bv, .and φ ψ => D0.and (tr fv bv φ) (tr fv bv ψ)
  | _, _, fv, bv, .or φ ψ => D0.or (tr fv bv φ) (tr fv bv ψ)
  | _, _, fv, bv, .all (.or (.nrel AdRel.mem v) B) =>
      D0.ball (trBd bv fv (v 1)) (tr (fun x => (fv x).castSucc) (bvExt bv) B)
  | _, _, fv, bv, .exs (.and (.rel AdRel.mem v) B) =>
      D0.bex (trBd bv fv (v 1)) (tr (fun x => (fv x).castSucc) (bvExt bv) B)
  | k, _, _, _, .all _ => trFalse k
  | k, _, _, _, .exs _ => trFalse k


theorem trBd_bShift {n k : ℕ} (bv : Fin n → Fin k) (fv : ℕ → Fin k) (t : Semiterm LAd ℕ n) :
    trBd bv fv (Rew.bShift t) = Bd.var (trTm bv fv t) := by
  cases t with
  | bvar i => simp [trBd, trTm]
  | fvar x => simp [trBd, trTm]
  | func g _ => exact Empty.elim g

theorem tr_ballAt {n k : ℕ} (fv : ℕ → Fin k) (bv : Fin n → Fin k) (t : Semiterm LAd ℕ n)
    (φ : Semiformula LAd ℕ (n + 1)) :
    tr fv bv (ballAt t φ) =
      D0.ball (Bd.var (trTm bv fv t)) (tr (fun x => (fv x).castSucc) (bvExt bv) φ) := by
  have h : tr fv bv (ballAt t φ) =
      D0.ball (trBd bv fv (Rew.bShift t)) (tr (fun x => (fv x).castSucc) (bvExt bv) φ) := rfl
  rw [h, trBd_bShift]

theorem tr_bexAt {n k : ℕ} (fv : ℕ → Fin k) (bv : Fin n → Fin k) (t : Semiterm LAd ℕ n)
    (φ : Semiformula LAd ℕ (n + 1)) :
    tr fv bv (bexAt t φ) =
      D0.bex (Bd.var (trTm bv fv t)) (tr (fun x => (fv x).castSucc) (bvExt bv) φ) := by
  have h : tr fv bv (bexAt t φ) =
      D0.bex (trBd bv fv (Rew.bShift t)) (tr (fun x => (fv x).castSucc) (bvExt bv) φ) := rfl
  rw [h, trBd_bShift]


theorem ext_bvExt {M : Type*} {k n : ℕ} (ρ : Fin k → M) (x : M) (bv : Fin n → Fin k) :
    (fun i => ext ρ x (bvExt bv i)) = (x :> fun i => ρ (bv i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [bvExt]
  · simp [bvExt]

theorem ext_fvExt {M : Type*} {k : ℕ} (ρ : Fin k → M) (x : M) (fv : ℕ → Fin k) :
    (fun j => ext ρ x (fv j).castSucc) = fun j => ρ (fv j) := by
  funext j; simp

theorem val_tr {M : Type*} (r : M → M → Prop) (P : M → Prop) {n k : ℕ} (fv : ℕ → Fin k)
    (bv : Fin n → Fin k) (ρ : Fin k → M) (t : Semiterm LAd ℕ n) :
    Semiterm.val (s := adStruc r P) (fun i => ρ (bv i)) (fun j => ρ (fv j)) t = ρ (trTm bv fv t) := by
  cases t with
  | bvar i => rfl
  | fvar j => rfl
  | func g _ => exact Empty.elim g

theorem RSTrue_ad_iff (R : Set Ordinal.{1}) {n : ℕ} (i : Fin n) (ρ : Fin n → T) :
    RSTrue R (RSS.base (D0.ad i) ρ) ↔ AdP R (ρ i) := by
  unfold AdP
  rw [RSTrue_ad, RSTrue_ad]
  rfl

theorem RSTrue_nmem_iff (R : Set Ordinal.{1}) {n : ℕ} (i j : Fin n) (ρ : Fin n → T) :
    RSTrue R (RSS.base (D0.nmem i j) ρ) ↔ ¬ Mem R (ρ i) (ρ j) := by
  rw [← RSTrue_mem_iff]
  exact RSTrue_neg R (RSS.base (D0.mem i j) ρ)

theorem RSTrue_nad_iff (R : Set Ordinal.{1}) {n : ℕ} (i : Fin n) (ρ : Fin n → T) :
    RSTrue R (RSS.base (D0.nad i) ρ) ↔ ¬ AdP R (ρ i) := by
  rw [← RSTrue_ad_iff]
  exact RSTrue_neg R (RSS.base (D0.ad i) ρ)

theorem RSTrue_true (R : Set Ordinal.{1}) {k : ℕ} (ρ : Fin k → T) : RSTrue R (RSS.base (trTrue k) ρ) := by
  unfold trTrue
  rw [RSTrue_ball]
  intro t
  exact absurd t.2 (by simp [resBd, T.level, T.L, PT.level])

theorem not_RSTrue_false (R : Set Ordinal.{1}) {k : ℕ} (ρ : Fin k → T) :
    ¬ RSTrue R (RSS.base (trFalse k) ρ) := by
  unfold trFalse
  rw [RSTrue_bex]
  rintro ⟨t, -⟩
  exact absurd t.2 (by simp [resBd, T.level, T.L, PT.level])

/-! ### Correctness of the translation -/

section Correct

variable (p : Params)

theorem ext_val {k : ℕ} (ρ : Fin k → RSModel p) (x : RSModel p) :
    (fun i => (ext ρ x i).1) = ext (fun i => (ρ i).1) x.1 := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

/-- the model-element version of a term below `c`. -/
def tlt_up (c : RSModel p) (t : Tlt c.1.level) : RSModel p := ⟨t.1, lt_trans t.2 c.2⟩

/-- bounded universal quantifier: RS reading versus model reading. -/
theorem ball_transfer (c : RSModel p) (Q : RSModel p → Prop) (S : T → Prop)
    (hQ : ∀ x y : RSModel p, Eqv p.R x.1 y.1 → (Q x ↔ Q y))
    (hS : ∀ x : RSModel p, S x.1 ↔ Q x) :
    (∀ t : Tlt c.1.level, RSTrue p.R (memInst t.1 c.1).neg ∨ S t.1) ↔
      ∀ x : RSModel p, RSModel.rel p x c → Q x := by
  constructor
  · intro h x hx
    obtain ⟨t, ht, he⟩ := hx
    rcases h t with h1 | h1
    · exact absurd ht ((RSTrue_neg p.R _).1 h1)
    · exact (hQ (tlt_up p c t) x he).1 ((hS (tlt_up p c t)).1 h1)
  · intro h t
    by_cases hm : RSTrue p.R (memInst t.1 c.1)
    · right
      exact (hS (tlt_up p c t)).2 (h (tlt_up p c t) ⟨t, hm, Eqv.refl p.R t.1⟩)
    · left
      exact (RSTrue_neg p.R _).2 hm

/-- bounded existential quantifier: RS reading versus model reading. -/
theorem bex_transfer (c : RSModel p) (Q : RSModel p → Prop) (S : T → Prop)
    (hQ : ∀ x y : RSModel p, Eqv p.R x.1 y.1 → (Q x ↔ Q y))
    (hS : ∀ x : RSModel p, S x.1 ↔ Q x) :
    (∃ t : Tlt c.1.level, RSTrue p.R (memInst t.1 c.1) ∧ S t.1) ↔
      ∃ x : RSModel p, RSModel.rel p x c ∧ Q x := by
  constructor
  · rintro ⟨t, ht, hs⟩
    exact ⟨tlt_up p c t, ⟨t, ht, Eqv.refl p.R t.1⟩, (hS (tlt_up p c t)).1 hs⟩
  · rintro ⟨x, ⟨t, ht, he⟩, hq⟩
    exact ⟨t, ht, (hS (tlt_up p c t)).2 ((hQ (tlt_up p c t) x he).2 hq)⟩

/-- consing equal elements: the environments `x :> b`, `y :> b` are `Eqm`-pointwise equal. -/
theorem cons_eqm' {n : ℕ} (x y : RSModel p) (hxy : Eqv p.R x.1 y.1) (b : Fin n → RSModel p) :
    ∀ i, Eqm (RSModel.rel p) ((x :> b) i) ((y :> b) i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (RSModel.eqm_iff p x y).2 hxy
  · exact Eqm.refl _

theorem tr_mem {n k : ℕ} (fv : ℕ → Fin k) (bv : Fin n → Fin k) (s t : Semiterm LAd ℕ n) :
    tr fv bv (memAt s t) = D0.mem (trTm bv fv s) (trTm bv fv t) := rfl

theorem tr_nmem {n k : ℕ} (fv : ℕ → Fin k) (bv : Fin n → Fin k) (s t : Semiterm LAd ℕ n) :
    tr fv bv (nmemAt s t) = D0.nmem (trTm bv fv s) (trTm bv fv t) := rfl

theorem tr_ad {n k : ℕ} (fv : ℕ → Fin k) (bv : Fin n → Fin k) (t : Semiterm LAd ℕ n) :
    tr fv bv (adAt t) = D0.ad (trTm bv fv t) := rfl

theorem tr_nad {n k : ℕ} (fv : ℕ → Fin k) (bv : Fin n → Fin k) (t : Semiterm LAd ℕ n) :
    tr fv bv (nadAt t) = D0.nad (trTm bv fv t) := rfl

theorem tr_and {n k : ℕ} (fv : ℕ → Fin k) (bv : Fin n → Fin k) (φ ψ : Semiformula LAd ℕ n) :
    tr fv bv (φ ⋏ ψ) = D0.and (tr fv bv φ) (tr fv bv ψ) := rfl

theorem tr_or {n k : ℕ} (fv : ℕ → Fin k) (bv : Fin n → Fin k) (φ ψ : Semiformula LAd ℕ n) :
    tr fv bv (φ ⋎ ψ) = D0.or (tr fv bv φ) (tr fv bv ψ) := rfl

theorem tr_verum {n k : ℕ} (fv : ℕ → Fin k) (bv : Fin n → Fin k) :
    tr fv bv (⊤ : Semiformula LAd ℕ n) = trTrue k := rfl

theorem tr_falsum {n k : ℕ} (fv : ℕ → Fin k) (bv : Fin n → Fin k) :
    tr fv bv (⊥ : Semiformula LAd ℕ n) = trFalse k := rfl

/-- **Correctness of the translation**: the RS truth of `tr φ` is the truth of `φ` in the model. -/
theorem tr_correct :
    ∀ {n : ℕ} {φ : Semiformula LAd ℕ n}, IsDelta0 φ →
    ∀ {k : ℕ} (fv : ℕ → Fin k) (bv : Fin n → Fin k) (ρ : Fin k → RSModel p),
      RSTrue p.R (RSS.base (tr fv bv φ) (fun i => (ρ i).1)) ↔
        Semiformula.Eval (s := adStruc (RSModel.rel p) (RSModel.ad p))
          (fun i => ρ (bv i)) (fun j => ρ (fv j)) φ := by
  intro n φ hφ
  induction hφ with
  | verum =>
    intro k fv bv ρ
    rw [tr_verum]
    exact iff_of_true (RSTrue_true p.R _) (by simp)
  | falsum =>
    intro k fv bv ρ
    rw [tr_falsum]
    exact iff_of_false (not_RSTrue_false p.R _) (by simp)
  | mem s t =>
    intro k fv bv ρ
    rw [tr_mem, RSTrue_mem_iff, eval_memAt, val_tr, val_tr]
    exact Iff.rfl
  | nmem s t =>
    intro k fv bv ρ
    rw [tr_nmem, RSTrue_nmem_iff, eval_nmemAt, val_tr, val_tr]
    exact Iff.rfl
  | ad t =>
    intro k fv bv ρ
    rw [tr_ad, RSTrue_ad_iff, eval_adAt, val_tr]
    exact Iff.rfl
  | nad t =>
    intro k fv bv ρ
    rw [tr_nad, RSTrue_nad_iff, eval_nadAt, val_tr]
    exact Iff.rfl
  | and _ _ ih₁ ih₂ =>
    intro k fv bv ρ
    rw [tr_and, RSTrue_band]
    exact and_congr (ih₁ fv bv ρ) (ih₂ fv bv ρ)
  | or _ _ ih₁ ih₂ =>
    intro k fv bv ρ
    rw [tr_or, RSTrue_bor]
    exact or_congr (ih₁ fv bv ρ) (ih₂ fv bv ρ)
  | @ball n t φ' hb ih =>
    intro k fv bv ρ
    rw [tr_ballAt, RSTrue_ball, eval_ballAt, val_tr]
    refine ball_transfer p (ρ (trTm bv fv t))
      (fun x => Semiformula.Eval (s := adStruc (RSModel.rel p) (RSModel.ad p))
        (x :> fun i => ρ (bv i)) (fun j => ρ (fv j)) φ')
      (fun t' => RSTrue p.R (RSS.base (tr (fun x => (fv x).castSucc) (bvExt bv) φ')
        (ext (fun i => (ρ i).1) t'))) ?_ ?_
    · intro x y hxy
      exact eval_congr_delta0 (RSModel.extOK p) hb _ _ _ _
        (cons_eqm' p x y hxy _) (fun j => Eqm.refl _)
    · intro x
      have h := ih (fun j => (fv j).castSucc) (bvExt bv) (ext ρ x)
      rw [ext_val, ext_bvExt, ext_fvExt] at h
      exact h
  | @bex n t φ' hb ih =>
    intro k fv bv ρ
    rw [tr_bexAt, RSTrue_bex, eval_bexAt, val_tr]
    refine bex_transfer p (ρ (trTm bv fv t))
      (fun x => Semiformula.Eval (s := adStruc (RSModel.rel p) (RSModel.ad p))
        (x :> fun i => ρ (bv i)) (fun j => ρ (fv j)) φ')
      (fun t' => RSTrue p.R (RSS.base (tr (fun x => (fv x).castSucc) (bvExt bv) φ')
        (ext (fun i => (ρ i).1) t'))) ?_ ?_
    · intro x y hxy
      exact eval_congr_delta0 (RSModel.extOK p) hb _ _ _ _
        (cons_eqm' p x y hxy _) (fun j => Eqm.refl _)
    · intro x
      have h := ih (fun j => (fv j).castSucc) (bvExt bv) (ext ρ x)
      rw [ext_val, ext_bvExt, ext_fvExt] at h
      exact h

/-- all level bounds produced by `tr` are `0`. -/
theorem tr_levLE :
    ∀ {n : ℕ} {φ : Semiformula LAd ℕ n}, IsDelta0 φ →
    ∀ {k : ℕ} (fv : ℕ → Fin k) (bv : Fin n → Fin k) (α : Ordinal.{1}),
      D0.LevLE α (tr fv bv φ) := by
  intro n φ hφ
  induction hφ with
  | verum =>
    intro k fv bv α
    rw [tr_verum]
    exact ⟨zero_le, trivial⟩
  | falsum =>
    intro k fv bv α
    rw [tr_falsum]
    exact ⟨zero_le, trivial⟩
  | mem s t => intro k fv bv α; rw [tr_mem]; exact trivial
  | nmem s t => intro k fv bv α; rw [tr_nmem]; exact trivial
  | ad t => intro k fv bv α; rw [tr_ad]; exact trivial
  | nad t => intro k fv bv α; rw [tr_nad]; exact trivial
  | and _ _ ih₁ ih₂ =>
    intro k fv bv α
    rw [tr_and]
    exact ⟨ih₁ fv bv α, ih₂ fv bv α⟩
  | or _ _ ih₁ ih₂ =>
    intro k fv bv α
    rw [tr_or]
    exact ⟨ih₁ fv bv α, ih₂ fv bv α⟩
  | @ball n t φ' hb ih =>
    intro k fv bv α
    rw [tr_ballAt]
    exact ih _ _ α
  | @bex n t φ' hb ih =>
    intro k fv bv α
    rw [tr_bexAt]
    exact ih _ _ α

end Correct

/-! ### Congruence of Δ₀-formulas, only at the free variables that occur -/

theorem eval_congr_fv {M : Type*} {r : M → M → Prop} {P : M → Prop} (hext : ExtOK r P) {n : ℕ}
    {φ : Semiformula LAd ℕ n} (hφ : IsDelta0 φ) (b b' : Fin n → M) (f f' : ℕ → M)
    (hb : ∀ i, Eqm r (b i) (b' i)) (hf : ∀ j, φ.FVar? j → Eqm r (f j) (f' j)) :
    Semiformula.Eval (s := adStruc r P) b f φ ↔ Semiformula.Eval (s := adStruc r P) b' f' φ := by
  classical
  let f'' : ℕ → M := fun j => if φ.FVar? j then f' j else f j
  have h1 : Semiformula.Eval (s := adStruc r P) b' f' φ ↔
      Semiformula.Eval (s := adStruc r P) b' f'' φ :=
    Semiformula.eval_iff_of_funEqOn φ (fun j hj => by simp [f'', hj])
  have h2 : ∀ j, Eqm r (f j) (f'' j) := by
    intro j
    by_cases hj : φ.FVar? j
    · simpa [f'', hj] using hf j hj
    · simpa [f'', hj] using Eqm.refl (f j)
  exact (eval_congr_delta0 hext hφ b b' f f'' hb h2).trans h1.symm

/-! ### Comprehension terms -/

/-- the comprehension term `[x ∈ L_α : B(x, a)]`. -/
def compT (α : Ordinal.{1}) {m : ℕ} (B : D0 (m + 1)) (a : Fin m → T) (h0 : 0 < α)
    (hB : D0.LevLE α B) (ha : ∀ i, (a i).level < α) (hO : D0.Occ (Fin.last m) B) : T :=
  ⟨PT.sep α B (fun i => (a i).1), ⟨h0, hB, fun i => ⟨(a i).2, ha i⟩, hO⟩⟩

theorem compT_level (α : Ordinal.{1}) {m : ℕ} (B : D0 (m + 1)) (a : Fin m → T) (h0 : 0 < α)
    (hB : D0.LevLE α B) (ha : ∀ i, (a i).level < α) (hO : D0.Occ (Fin.last m) B) :
    (compT α B a h0 hB ha hO).level = α := rfl

/-- membership in a comprehension term. -/
theorem mem_compT_iff (R : Set Ordinal.{1}) (α : Ordinal.{1}) {m : ℕ} (B : D0 (m + 1))
    (a : Fin m → T) (h0 : 0 < α) (hB : D0.LevLE α B) (ha : ∀ i, (a i).level < α)
    (hO : D0.Occ (Fin.last m) B) (x : T) :
    Mem R x (compT α B a h0 hB ha hO) ↔
      ∃ t : Tlt α, RSTrue R (RSS.base B (ext a t.1)) ∧ Eqv R t.1 x :=
  Iff.rfl

/-! ### A finite bound below a successor limit -/

theorem exists_bound (κ : Ordinal.{1}) (hlim : Order.IsSuccLimit κ) (g : ℕ → Ordinal.{1})
    (hg : ∀ j, g j < κ) (e : Ordinal.{1}) (he : e < κ) :
    ∀ N : ℕ, ∃ α : Ordinal.{1}, 0 < α ∧ α < κ ∧ (∀ j, j < N → g j < α) ∧ e < α := by
  intro N
  induction N with
  | zero =>
    refine ⟨Order.succ e, lt_of_le_of_lt zero_le (Order.lt_succ e), hlim.succ_lt he, ?_,
      Order.lt_succ e⟩
    intro j hj
    exact absurd hj (Nat.not_lt_zero j)
  | succ N ih =>
    obtain ⟨α₀, h0, hκ, hj, he'⟩ := ih
    refine ⟨max α₀ (Order.succ (g N)), lt_of_lt_of_le h0 (le_max_left _ _),
      max_lt hκ (hlim.succ_lt (hg N)), ?_, lt_of_lt_of_le he' (le_max_left _ _)⟩
    intro j hjN
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjN with h | h
    · exact lt_of_lt_of_le (hj j h) (le_max_left _ _)
    · subst h
      exact lt_of_lt_of_le (Order.lt_succ _) (le_max_right _ _)

/-! ### The Sep core -/

section Sep

variable (p : Params)

/-- the body of the separation term: `x ∈ w ∧ tr φ(x)`; `x` is the last variable, `w` the
parameter in slot `Fin.last N`. -/
def sepTermBody (N : ℕ) (fv : ℕ → Fin (N + 2)) (φ : Semiformula LAd ℕ 1) : D0 (N + 2) :=
  D0.and (D0.mem (Fin.last (N + 1)) (Fin.last N).castSucc)
    (tr fv (fun _ => Fin.last (N + 1)) φ)

theorem sepTermBody_levLE {N : ℕ} (fv : ℕ → Fin (N + 2)) {φ : Semiformula LAd ℕ 1} (hφ : IsDelta0 φ)
    (α : Ordinal.{1}) : D0.LevLE α (sepTermBody N fv φ) :=
  ⟨trivial, tr_levLE hφ fv _ α⟩

theorem sepTermBody_occ {N : ℕ} (fv : ℕ → Fin (N + 2)) (φ : Semiformula LAd ℕ 1) :
    D0.Occ (Fin.last (N + 1)) (sepTermBody N fv φ) :=
  Or.inl (Or.inl rfl)

/-- truth of the separation body at a candidate element. -/
theorem sepTermBody_iff {N : ℕ} (fv : ℕ → Fin (N + 2)) {φ : Semiformula LAd ℕ 1} (hφ : IsDelta0 φ)
    (g : Fin (N + 1) → RSModel p) (t : RSModel p) :
    RSTrue p.R (RSS.base (sepTermBody N fv φ) (ext (fun i => (g i).1) t.1)) ↔
      Mem p.R t.1 (g (Fin.last N)).1 ∧
      Semiformula.Eval (s := adStruc (RSModel.rel p) (RSModel.ad p)) ![t]
        (fun j => ext g t (fv j)) φ := by
  have e : ext (fun i => (g i).1) t.1 = fun i => (ext g t i).1 := (ext_val p g t).symm
  unfold sepTermBody
  rw [e, RSTrue_band, RSTrue_mem_iff]
  have e1 : (fun i : Fin 1 => ext g t ((fun _ => Fin.last (N + 1)) i)) = ![t] := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    simp
  have h2 := tr_correct p hφ fv (fun _ => Fin.last (N + 1)) (ext g t)
  rw [e1] at h2
  rw [h2]
  simp only [ext_last, ext_castSucc]

/-- **Separation core**: for `κ` a successor limit `≤ lam`, the Δ₀-separation set of any `w` and any
parameters represented below `κ` is again represented below `κ`. -/
theorem core_sep (κ : Ordinal.{1}) (hlim : Order.IsSuccLimit κ) (hκl : κ ≤ p.lam)
    (φ : Semiformula LAd ℕ 1) (hφ : IsDelta0 φ) (f : ℕ → RSModel p) (w : RSModel p)
    (hf : ∀ j, ∃ s : T, s.level < κ ∧ Eqv p.R s (f j).1)
    (hw : ∃ s : T, s.level < κ ∧ Eqv p.R s w.1) :
    ∃ y : RSModel p, y.1.level < κ ∧
      (∀ x : RSModel p, RSModel.rel p x y →
          RSModel.rel p x w ∧
            Semiformula.Eval (s := adStruc (RSModel.rel p) (RSModel.ad p)) ![x] f φ) ∧
      (∀ x : RSModel p, RSModel.rel p x w →
          Semiformula.Eval (s := adStruc (RSModel.rel p) (RSModel.ad p)) ![x] f φ →
            RSModel.rel p x y) := by
  choose f' hf'lev hf'eqv using hf
  obtain ⟨w', hw'lev, hw'eqv⟩ := hw
  obtain ⟨α, hα0, hακ, hαf, hαw⟩ :=
    exists_bound κ hlim (fun j => (f' j).level) hf'lev w'.level hw'lev φ.fvSup
  have hαl : α < p.lam := lt_of_lt_of_le hακ hκl
  -- model elements for the representatives
  let fM : ℕ → RSModel p := fun j => ⟨f' j, lt_of_lt_of_le (hf'lev j) hκl⟩
  let wM : RSModel p := ⟨w', lt_of_lt_of_le hw'lev hκl⟩
  let N : ℕ := φ.fvSup
  let g : Fin (N + 1) → RSModel p := ext (fun j : Fin N => fM j.1) wM
  let fv : ℕ → Fin (N + 2) := fun j =>
    if h : j < N then (⟨j, h⟩ : Fin N).castSucc.castSucc else Fin.last (N + 1)
  have hgl : (g (Fin.last N)).1 = w' := by
    show (ext (fun j : Fin N => fM j.1) wM (Fin.last N)).1 = w'
    rw [ext_last]
  have hgc : ∀ j : Fin N, g j.castSucc = fM j.1 := by
    intro j
    show ext (fun j : Fin N => fM j.1) wM j.castSucc = fM j.1
    rw [ext_castSucc]
  have hg : ∀ i, (g i).1.level < α := by
    intro i
    induction i using Fin.lastCases with
    | last => rw [hgl]; exact hαw
    | cast j => rw [hgc]; exact hαf j.1 j.2
  have hfv : ∀ (t : RSModel p) (j : ℕ), j < N → ext g t (fv j) = fM j := by
    intro t j hj
    have h1 : fv j = (⟨j, hj⟩ : Fin N).castSucc.castSucc := dif_pos hj
    rw [h1, ext_castSucc, hgc]
  let B : D0 (N + 2) := sepTermBody N fv φ
  let term : T := compT α B (fun i => (g i).1) hα0 (sepTermBody_levLE fv hφ α) hg (sepTermBody_occ fv φ)
  have hterm : term.level < p.lam := hαl
  have hmem : ∀ x : T, Mem p.R x term ↔
      ∃ t : Tlt α, RSTrue p.R (RSS.base B (ext (fun i => (g i).1) t.1)) ∧ Eqv p.R t.1 x :=
    fun x => mem_compT_iff p.R α B (fun i => (g i).1) hα0 (sepTermBody_levLE fv hφ α) hg
      (sepTermBody_occ fv φ) x
  -- the key equivalence for `Tlt α`
  have key : ∀ t : Tlt α, RSTrue p.R (RSS.base B (ext (fun i => (g i).1) t.1)) ↔
      Mem p.R t.1 w' ∧ Semiformula.Eval (s := adStruc (RSModel.rel p) (RSModel.ad p)) ![⟨t.1, lt_trans t.2 hαl⟩]
        (fun j => ext g ⟨t.1, lt_trans t.2 hαl⟩ (fv j)) φ := by
    intro t
    rw [← hgl]
    exact sepTermBody_iff p fv hφ g ⟨t.1, lt_trans t.2 hαl⟩
  -- congruence of the free-variable environment
  have hcong : ∀ (t x : RSModel p), Eqv p.R t.1 x.1 →
      (Semiformula.Eval (s := adStruc (RSModel.rel p) (RSModel.ad p)) ![t]
          (fun j => ext g t (fv j)) φ ↔
        Semiformula.Eval (s := adStruc (RSModel.rel p) (RSModel.ad p)) ![x] f φ) := by
    intro t x htx
    refine eval_congr_fv (RSModel.extOK p) hφ _ _ _ _ ?_ ?_
    · intro i
      rw [Fin.fin_one_eq_zero i]
      exact (RSModel.eqm_iff p t x).2 htx
    · intro j hj
      have hjN : j < N := Semiformula.lt_fvSup_of_fvar? hj
      rw [hfv t j hjN]
      exact (RSModel.eqm_iff p (fM j) (f j)).2 (hf'eqv j)
  refine ⟨⟨term, hterm⟩, hακ, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht, hte⟩ := (hmem x.1).1 hx
    obtain ⟨hmt, hev⟩ := (key t).1 ht
    refine ⟨?_, ?_⟩
    · exact Mem.congr_right p.R hw'eqv (Mem.congr_left p.R hte hmt)
    · exact (hcong ⟨t.1, lt_trans t.2 hαl⟩ x hte).1 hev
  · intro x hxw hev
    have hxw' : Mem p.R x.1 w' := Mem.congr_right p.R (Eqv.symm p.R hw'eqv) hxw
    obtain ⟨s, hs, hse⟩ := hxw'
    have hsα : s.1.level < α := lt_trans s.2 hαw
    let t : Tlt α := ⟨s.1, hsα⟩
    have hmt : Mem p.R t.1 w' := ⟨s, hs, Eqv.refl p.R s.1⟩
    have hev' := (hcong ⟨t.1, lt_trans t.2 hαl⟩ x hse).2 hev
    exact (hmem x.1).2 ⟨t, (key t).2 ⟨hmt, hev'⟩, hse⟩

end Sep


end OrdinalAnalysis.KPi.Sound
