module

public import OrdinalAnalysis.KPi.RS.StarAx2

/-!
# The RS calculus, part 18: Theorem 2.9 (a), `(Δ₀-Sep)`: definitions and syntactic lemmas

* `Bd.shiftN`, `ctxK`, `closeB` : closing a formula `D0 (m + k)` over `k` quantifiers `∀z∈b`;
* `sepCore`, `sepD`            : `(Δ₀-Sep)^b` for `φ(z₁..z_k, x)`;
* `sepTerm`                    : the term `[x ∈ L_δ : x ∈ a ∧ φ(x, c⃗)]`;
* syntactic lemmas on `LevLE`, `kD`, `rename`.
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}} {σ : Ordinal.{1}}

/-! ### `LevLE` and `kD` under renaming -/

theorem levLE_mono : ∀ {n : ℕ} (A : D0 n) {α β : Ordinal.{1}}, D0.LevLE α A → α ≤ β →
    D0.LevLE β A
  | _, .mem _ _, _, _, _, _ => trivial
  | _, .nmem _ _, _, _, _, _ => trivial
  | _, .ad _, _, _, _, _ => trivial
  | _, .nad _, _, _, _, _ => trivial
  | _, .and A B, _, _, h, hle => ⟨levLE_mono A h.1 hle, levLE_mono B h.2 hle⟩
  | _, .or A B, _, _, h, hle => ⟨levLE_mono A h.1 hle, levLE_mono B h.2 hle⟩
  | _, .bex (.var _) A, _, _, h, hle => levLE_mono A h hle
  | _, .bex (.lev _) A, _, _, h, hle => ⟨le_trans h.1 hle, levLE_mono A h.2 hle⟩
  | _, .ball (.var _) A, _, _, h, hle => levLE_mono A h hle
  | _, .ball (.lev _) A, _, _, h, hle => ⟨le_trans h.1 hle, levLE_mono A h.2 hle⟩

theorem levLE_rename : ∀ {m k : ℕ} (f : Fin m → Fin k) (A : D0 m) {α : Ordinal.{1}},
    D0.LevLE α A → D0.LevLE α (A.rename f)
  | _, _, _, .mem _ _, _, _ => trivial
  | _, _, _, .nmem _ _, _, _ => trivial
  | _, _, _, .ad _, _, _ => trivial
  | _, _, _, .nad _, _, _ => trivial
  | _, _, f, .and A B, _, h => ⟨levLE_rename f A h.1, levLE_rename f B h.2⟩
  | _, _, f, .or A B, _, h => ⟨levLE_rename f A h.1, levLE_rename f B h.2⟩
  | _, _, f, .bex (.var _) A, _, h => levLE_rename (liftF f) A h
  | _, _, f, .bex (.lev _) A, _, h => ⟨h.1, levLE_rename (liftF f) A h.2⟩
  | _, _, f, .ball (.var _) A, _, h => levLE_rename (liftF f) A h
  | _, _, f, .ball (.lev _) A, _, h => ⟨h.1, levLE_rename (liftF f) A h.2⟩

theorem levLE_neg : ∀ {n : ℕ} (A : D0 n) {α : Ordinal.{1}}, D0.LevLE α A → D0.LevLE α A.neg
  | _, .mem _ _, _, _ => trivial
  | _, .nmem _ _, _, _ => trivial
  | _, .ad _, _, _ => trivial
  | _, .nad _, _, _ => trivial
  | _, .and A B, _, h => ⟨levLE_neg A h.1, levLE_neg B h.2⟩
  | _, .or A B, _, h => ⟨levLE_neg A h.1, levLE_neg B h.2⟩
  | _, .bex (.var _) A, _, h => levLE_neg A h
  | _, .bex (.lev _) A, _, h => ⟨h.1, levLE_neg A h.2⟩
  | _, .ball (.var _) A, _, h => levLE_neg A h
  | _, .ball (.lev _) A, _, h => ⟨h.1, levLE_neg A h.2⟩

/-- `k` of a formula with level constants `≤ 0` lies in any set `S` containing `0` and the `k` of
the environment. -/
theorem kD_sub : ∀ {n : ℕ} (A : D0 n) (e : Fin n → Set Ordinal.{1}) (S : Set Ordinal.{1}),
    (∀ i, e i ⊆ S) → D0.LevLE 0 A → (0 : Ordinal.{1}) ∈ S → kD A e ⊆ S
  | _, .mem i j, e, S, he, _, _ => Set.union_subset (he i) (he j)
  | _, .nmem i j, e, S, he, _, _ => Set.union_subset (he i) (he j)
  | _, .ad i, e, S, he, _, _ => he i
  | _, .nad i, e, S, he, _, _ => he i
  | _, .and A B, e, S, he, h, h0 =>
    Set.union_subset (kD_sub A e S he h.1 h0) (kD_sub B e S he h.2 h0)
  | _, .or A B, e, S, he, h, h0 =>
    Set.union_subset (kD_sub A e S he h.1 h0) (kD_sub B e S he h.2 h0)
  | _, .bex (.var j) A, e, S, he, h, h0 =>
    Set.union_subset (he j) (kD_sub A (ext e ∅) S (by
      intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using he i) h h0)
  | _, .bex (.lev γ) A, e, S, he, h, h0 =>
    Set.union_subset (by
      intro ξ hξ
      have hγ : γ = 0 := le_antisymm h.1 zero_le
      have : ξ = γ := hξ
      rw [this, hγ]; exact h0)
      (kD_sub A (ext e ∅) S (by
      intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using he i) h.2 h0)
  | _, .ball (.var j) A, e, S, he, h, h0 =>
    Set.union_subset (he j) (kD_sub A (ext e ∅) S (by
      intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using he i) h h0)
  | _, .ball (.lev γ) A, e, S, he, h, h0 =>
    Set.union_subset (by
      intro ξ hξ
      have hγ : γ = 0 := le_antisymm h.1 zero_le
      have : ξ = γ := hξ
      rw [this, hγ]; exact h0)
      (kD_sub A (ext e ∅) S (by
      intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using he i) h.2 h0)

/-! ### contexts and closures -/

/-- the bound `b` seen under `k` further binders. -/
def Bd.shiftN {m : ℕ} (b : Bd m) : (k : ℕ) → Bd (m + k)
  | 0 => b
  | k + 1 => (Bd.shiftN b k).shift

/-- the context `ρ` extended by the parameters `c`. -/
def ctxK {m : ℕ} (ρ : Fin m → T) : (k : ℕ) → (Fin k → T) → Fin (m + k) → T
  | 0, _ => ρ
  | k + 1, c => ext (ctxK ρ k (fun i => c i.castSucc)) (c (Fin.last k))

theorem resBd_shiftN {m : ℕ} (b : Bd m) (ρ : Fin m → T) :
    ∀ (k : ℕ) (c : Fin k → T), resBd (b.shiftN k) (ctxK ρ k c) = resBd b ρ
  | 0, c => rfl
  | k + 1, c => by
    show resBd (Bd.shiftN b k).shift (ext (ctxK ρ k (fun i => c i.castSucc)) (c (Fin.last k))) = _
    rw [resBd_shift]
    exact resBd_shiftN b ρ k _

theorem ctxK_succ_ext {m : ℕ} (ρ : Fin m → T) (k : ℕ) (c : Fin k → T) (t : T) :
    ctxK ρ (k + 1) (ext c t) = ext (ctxK ρ k c) t := by
  show ext (ctxK ρ k (fun i => ext c t i.castSucc)) (ext c t (Fin.last k)) = _
  simp

theorem ctxK_natAdd {m : ℕ} (ρ : Fin m → T) : ∀ (k : ℕ) (c : Fin k → T) (j : Fin k),
    ctxK ρ k c (Fin.natAdd m j) = c j
  | 0, c, j => j.elim0
  | k + 1, c, j => by
    induction j using Fin.lastCases with
    | last => simp [ctxK]
    | cast j =>
      have := ctxK_natAdd ρ k (fun i => c i.castSucc) j
      show ext (ctxK ρ k fun i => c i.castSucc) (c (Fin.last k)) (Fin.natAdd m j.castSucc) =
        c j.castSucc
      rw [show Fin.natAdd m j.castSucc = (Fin.natAdd m j).castSucc from rfl, ext_castSucc]
      exact this

/-- `∀z₁∈b … ∀z_k∈b φ`. -/
def closeB {m : ℕ} (b : Bd m) : (k : ℕ) → D0 (m + k) → D0 m
  | 0, φ => φ
  | k + 1, φ => closeB b k (D0.ball (b.shiftN k) φ)

theorem star_closeB {m : ℕ} (b : Bd m) (ρ : Fin m → T) (lam : Ordinal.{1})
    (hb : resBd b ρ = T.L lam) : ∀ (k : ℕ) (φ : D0 (m + k)) {Δ : Set RSS},
    (∀ c : Fin k → T, (∀ i, (c i).level < lam) → ∀ Δ' : Set RSS,
      (∀ i, (memInst (c i) (T.L lam)).neg ∈ Δ') → RSS.base φ (ctxK ρ k c) ∈ Δ' →
        Star R σ Δ') →
    RSS.base (closeB b k φ) ρ ∈ Δ → Star R σ Δ := by
  intro k
  induction k with
  | zero =>
    intro φ Δ H hA
    exact H Fin.elim0 (fun i => i.elim0) Δ (fun i => i.elim0) hA
  | succ k ih =>
    intro φ Δ H hA
    refine ih (D0.ball (b.shiftN k) φ) (fun c' hc' Δ' hmem hA' => ?_) hA
    refine star_ball' hA' (by rw [resBd_shiftN, hb]) (fun t ht => ?_)
    have hct := H (ext c' t)
    rw [ctxK_succ_ext] at hct
    refine hct (fun i => ?_) _ (fun i => ?_) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · induction i using Fin.lastCases with
      | last => simpa [level_L] using ht
      | cast j => simpa using hc' j
    · induction i using Fin.lastCases with
      | last => simp
      | cast j => simp [hmem j]

end OrdinalAnalysis.KPi.RS
