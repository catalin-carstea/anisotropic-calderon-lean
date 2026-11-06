import Calderon.FiniteHilbertBlockMatrix
import Calderon.FiniteWeightedMidpointBound

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.SpectralSylvester

variable {E : ℕ → Type*} [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℝ (E k)]

lemma finite_lp_midpoint_direction_bound
    (T0 T1 : lp E 2 →L[ℝ] lp E 2) (s : Finset ℕ) (r : ℕ → ℝ)
    (hr : ∀ k ∈ s, 0 < r k)
    (hc : ∀ i ∈ s, ∀ j ∈ s, ∀ z : E j,
      (T1 (lp.single (E := E) 2 j z)) i =
        ((r i)^2/(r j)^2) • (T0 (lp.single (E := E) 2 j z)) i)
    (a b : ∀ k, E k) (ha : ∀ k ∈ s, ‖a k‖ ≤ 1) (hb : ∀ k ∈ s, ‖b k‖ ≤ 1)
    (M0 M1 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hT0 : ‖T0‖ ≤ M0) (hT1 : ‖T1‖ ≤ M1)
    (x y : ℕ → ℝ) :
    |∑ i ∈ s, ∑ j ∈ s, (r i/r j)*⟪(T0 (lp.single (E := E) 2 j (a j))) i,b i⟫_ℝ*x j*y i| ≤
      ((M0+M1)/2)*Real.sqrt (∑ j ∈ s, (x j)^2)*Real.sqrt (∑ i ∈ s, (y i)^2) := by
  let K : ℕ → ℕ → ℝ := fun i j => r i*r j*⟪(T0 (lp.single (E := E) 2 j (a j))) i,b i⟫_ℝ
  have hk0 (i : ℕ) (hi : i ∈ s) (j : ℕ) (hj : j ∈ s) :
      K i j/(r i*r j) = ⟪(T0 (lp.single (E := E) 2 j (a j))) i,b i⟫_ℝ := by
    dsimp [K]
    have hi0 := (hr i hi).ne'
    have hj0 := (hr j hj).ne'
    field_simp
  have hk1 (i : ℕ) (hi : i ∈ s) (j : ℕ) (hj : j ∈ s) :
      r i*K i j/(r j)^3 = ⟪(T1 (lp.single (E := E) 2 j (a j))) i,b i⟫_ℝ := by
    rw [hc i hi j hj,real_inner_smul_left]
    dsimp [K]
    have hj0 := (hr j hj).ne'
    field_simp
    <;> ring
  have h0 (x y : ℕ → ℝ) :
      |∑ i ∈ s, ∑ j ∈ s, (K i j/(r i*r j))*x j*y i| ≤
        (M0/2)*((∑ i ∈ s, (x i)^2)+∑ i ∈ s, (y i)^2) := by
    have he : (∑ i ∈ s, ∑ j ∈ s, (K i j/(r i*r j))*x j*y i) =
        ∑ i ∈ s, ∑ j ∈ s, ⟪(T0 (lp.single (E := E) 2 j (a j))) i,b i⟫_ℝ*x j*y i := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hk0 i hi j hj]
    rw [he]
    exact finite_lp_direction_matrix_quadratic_bound T0 s a b ha hb M0 hM0 hT0 x y
  have h1 (x y : ℕ → ℝ) :
      |∑ i ∈ s, ∑ j ∈ s, (r i*K i j/(r j)^3)*x j*y i| ≤
        (M1/2)*((∑ i ∈ s, (x i)^2)+∑ i ∈ s, (y i)^2) := by
    have he : (∑ i ∈ s, ∑ j ∈ s, (r i*K i j/(r j)^3)*x j*y i) =
        ∑ i ∈ s, ∑ j ∈ s, ⟪(T1 (lp.single (E := E) 2 j (a j))) i,b i⟫_ℝ*x j*y i := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hk1 i hi j hj]
    rw [he]
    exact finite_lp_direction_matrix_quadratic_bound T1 s a b ha hb M1 hM1 hT1 x y
  have h := finite_weighted_midpoint_form_bound s r hr K M0 M1 hM0 hM1 h0 h1 x y
  have he : (∑ i ∈ s, ∑ j ∈ s, (K i j/(r j)^2)*x j*y i) =
      ∑ i ∈ s, ∑ j ∈ s, (r i/r j)*⟪(T0 (lp.single (E := E) 2 j (a j))) i,b i⟫_ℝ*x j*y i := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [K]
    have hj0 := (hr j hj).ne'
    field_simp
    <;> ring
  rwa [he] at h

lemma inner_lp_single_normalize
    (T : lp E 2 →L[ℝ] lp E 2) (i j : ℕ) (u : E j) (v : E i) :
    ⟪(T (lp.single (E := E) 2 j u)) i,v⟫_ℝ =
      ⟪(T (lp.single (E := E) 2 j (NormedSpace.normalize u))) i,
        NormedSpace.normalize v⟫_ℝ*‖u‖*‖v‖ := by
  calc
    _ = ⟪(T (lp.single (E := E) 2 j (‖u‖ • NormedSpace.normalize u))) i,
        ‖v‖ • NormedSpace.normalize v⟫_ℝ := by rw [NormedSpace.norm_smul_normalize,NormedSpace.norm_smul_normalize]
    _ = _ := by
      rw [lp.single_smul,map_smul,lp.coeFn_smul,Pi.smul_apply,
        real_inner_smul_left,real_inner_smul_right]
      ring

lemma finite_lp_midpoint_block_bound
    (T0 T1 : lp E 2 →L[ℝ] lp E 2) (s : Finset ℕ) (r : ℕ → ℝ)
    (hr : ∀ k ∈ s, 0 < r k)
    (hc : ∀ i ∈ s, ∀ j ∈ s, ∀ z : E j,
      (T1 (lp.single (E := E) 2 j z)) i =
        ((r i)^2/(r j)^2) • (T0 (lp.single (E := E) 2 j z)) i)
    (M0 M1 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hT0 : ‖T0‖ ≤ M0) (hT1 : ‖T1‖ ≤ M1)
    (u v : ∀ k, E k) :
    |∑ i ∈ s, ∑ j ∈ s, (r i/r j)*⟪(T0 (lp.single (E := E) 2 j (u j))) i,v i⟫_ℝ| ≤
      ((M0+M1)/2)*Real.sqrt (∑ j ∈ s, ‖u j‖^2)*Real.sqrt (∑ i ∈ s, ‖v i‖^2) := by
  have h := finite_lp_midpoint_direction_bound T0 T1 s r hr hc
    (fun k => NormedSpace.normalize (u k)) (fun k => NormedSpace.normalize (v k))
    (fun k hk => norm_normalize_le_one (u k)) (fun k hk => norm_normalize_le_one (v k))
    M0 M1 hM0 hM1 hT0 hT1 (fun k => ‖u k‖) (fun k => ‖v k‖)
  have he : (∑ i ∈ s, ∑ j ∈ s, (r i/r j)*⟪(T0 (lp.single (E := E) 2 j (u j))) i,v i⟫_ℝ) =
      ∑ i ∈ s, ∑ j ∈ s, (r i/r j)*
        ⟪(T0 (lp.single (E := E) 2 j (NormedSpace.normalize (u j)))) i,NormedSpace.normalize (v i)⟫_ℝ*‖u j‖*‖v i‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [inner_lp_single_normalize]
    ring
  rw [he]
  exact h

end OAI.AnisotropicCalderon.SpectralSylvester
