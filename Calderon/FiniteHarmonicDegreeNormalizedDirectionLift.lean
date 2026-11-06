import Calderon.FiniteDegreeSylvesterSelectedEnergy
import Calderon.FiniteHilbertBlockMatrix
import Calderon.SphereHilbertDecomposition

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SpectralSylvester
open SphereHarmonic

/-! Actual probability-L2 harmonic-block normalized directions, preserving degreeN.
The generic Casimir product bound is taken as a hypothesis. -/

lemma finite_harmonic_weighted_scaled_direction_energy_le
    (s : Finset ℕ) (a : ∀ k, harmonicSphereSubspace k)
    (ha : ∀ k ∈ s, ‖a k‖ ≤ 1) (w x : ℕ → ℝ) (hw : ∀ k ∈ s, 0 ≤ w k) :
    (∑ k ∈ s, w k*‖x k • a k‖^2) ≤ ∑ k ∈ s, w k*x k^2 := by
  apply Finset.sum_le_sum
  intro k hk
  have hsq : ‖a k‖^2 ≤ 1 := by nlinarith [norm_nonneg (a k), ha k hk]
  have hNorm : ‖x k • a k‖^2 ≤ x k^2 := by
    calc
      _ = x k^2*‖a k‖^2 := by rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      _ ≤ x k^2*1 := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = _ := mul_one _
  exact mul_le_mul_of_nonneg_left hNorm (hw k hk)

lemma finite_harmonic_degree_half_form_bound_of_casimir_product_bound
    (s : Finset ℕ)
    (K : ∀ m n : ℕ, harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m)
    (M : ℝ) (hM : 0 ≤ M)
    (hCasimir : ∀ x y : ∀ k, harmonicSphereSubspace k,
      |∑ m ∈ s, ∑ n ∈ s,
        (((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1))*⟪K m n (x n),y m⟫_ℝ)| ≤
      M*Real.sqrt (∑ k ∈ s, (1+(k:ℝ)*((k:ℝ)+1))*‖x k‖^2)*
        Real.sqrt (∑ k ∈ s, (1+(k:ℝ)*((k:ℝ)+1))*‖y k‖^2))
    (u v : ∀ k, harmonicSphereSubspace k) :
    |∑ m ∈ s, ∑ n ∈ s, ((m:ℝ)-(n:ℝ))*⟪K m n (u n),v m⟫_ℝ| ≤
      2*M*Real.sqrt (∑ k ∈ s, (1+(k:ℝ))*‖u k‖^2)*
        Real.sqrt (∑ k ∈ s, (1+(k:ℝ))*‖v k‖^2) := by
  let a (k : ℕ) : harmonicSphereSubspace k := NormedSpace.normalize (u k)
  let b (k : ℕ) : harmonicSphereSubspace k := NormedSpace.normalize (v k)
  let G (m n : ℕ) : ℝ := ⟪K m n (a n),b m⟫_ℝ
  have ha : ∀ k ∈ s, ‖a k‖ ≤ 1 := fun k _ => norm_normalize_le_one (u k)
  have hb : ∀ k ∈ s, ‖b k‖ ≤ 1 := fun k _ => norm_normalize_le_one (v k)
  have hInner (x y : ℕ → ℝ) (m n : ℕ) :
      ⟪K m n (x n • a n),y m • b m⟫_ℝ = G m n*x n*y m := by
    have hMap : K m n (x n • a n) = x n • K m n (a n) :=
      (K m n).map_smul (x n) (a n)
    have hLeft : ⟪x n • K m n (a n),y m • b m⟫_ℝ =
        x n * ⟪K m n (a n),y m • b m⟫_ℝ :=
      real_inner_smul_left (K m n (a n)) (y m • b m) (x n)
    have hRight : ⟪K m n (a n),y m • b m⟫_ℝ = y m * G m n :=
      real_inner_smul_right (K m n (a n)) (b m) (y m)
    calc
      _ = ⟪x n • K m n (a n),y m • b m⟫_ℝ :=
        congrArg (fun z : harmonicSphereSubspace m => ⟪z,y m • b m⟫_ℝ) hMap
      _ = x n * ⟪K m n (a n),y m • b m⟫_ℝ := hLeft
      _ = x n * (y m * G m n) := congrArg (fun t : ℝ => x n*t) hRight
      _ = _ := by ring
  have hScalar : ∀ x y : ℕ → ℝ,
      |∑ m ∈ s, ∑ n ∈ s,
        (((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1))*G m n*x n*y m)| ≤
      M*Real.sqrt (∑ k ∈ s, (1+(k:ℝ)*((k:ℝ)+1))*x k^2)*
        Real.sqrt (∑ k ∈ s, (1+(k:ℝ)*((k:ℝ)+1))*y k^2) := by
    intro x y
    have hSame : (∑ m ∈ s, ∑ n ∈ s,
        (((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1))*⟪K m n (x n • a n),y m • b m⟫_ℝ)) =
        ∑ m ∈ s, ∑ n ∈ s,
          (((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1))*G m n*x n*y m) := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      rw [hInner]
      ring
    have hX : (∑ k ∈ s, (1+(k:ℝ)*((k:ℝ)+1))*‖x k • a k‖^2) ≤
        ∑ k ∈ s, (1+(k:ℝ)*((k:ℝ)+1))*x k^2 :=
      finite_harmonic_weighted_scaled_direction_energy_le s a ha
        (fun k => 1+(k:ℝ)*((k:ℝ)+1)) x (fun k _ => by positivity)
    have hY : (∑ k ∈ s, (1+(k:ℝ)*((k:ℝ)+1))*‖y k • b k‖^2) ≤
        ∑ k ∈ s, (1+(k:ℝ)*((k:ℝ)+1))*y k^2 :=
      finite_harmonic_weighted_scaled_direction_energy_le s b hb
        (fun k => 1+(k:ℝ)*((k:ℝ)+1)) y (fun k _ => by positivity)
    have hProd := mul_le_mul (Real.sqrt_le_sqrt hX) (Real.sqrt_le_sqrt hY)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc
      _ ≤ M*Real.sqrt (∑ k ∈ s, (1+(k:ℝ)*((k:ℝ)+1))*‖x k • a k‖^2)*
          Real.sqrt (∑ k ∈ s, (1+(k:ℝ)*((k:ℝ)+1))*‖y k • b k‖^2) :=
        (congrArg abs hSame).symm.trans_le (hCasimir (fun k => x k • a k) (fun k => y k • b k))
      _ = M*(Real.sqrt (∑ k ∈ s, (1+(k:ℝ)*((k:ℝ)+1))*‖x k • a k‖^2)*
          Real.sqrt (∑ k ∈ s, (1+(k:ℝ)*((k:ℝ)+1))*‖y k • b k‖^2)) := by ring
      _ ≤ M*(Real.sqrt (∑ k ∈ s, (1+(k:ℝ)*((k:ℝ)+1))*x k^2)*
          Real.sqrt (∑ k ∈ s, (1+(k:ℝ)*((k:ℝ)+1))*y k^2)) :=
        mul_le_mul_of_nonneg_left hProd hM
      _ = _ := by ring
  have hScalarBound := finite_degree_commutator_half_form_bound_of_casimir_product_bound
    s id G M hM hScalar (fun k => ‖u k‖) (fun k => ‖v k‖)
  have hReconstruct (m n : ℕ) : ⟪K m n (u n),v m⟫_ℝ = G m n*‖u n‖*‖v m‖ := by
    have h := congrArg₂
      (fun x : harmonicSphereSubspace n => fun y : harmonicSphereSubspace m => ⟪K m n x,y⟫_ℝ)
      (NormedSpace.norm_smul_normalize (u n)) (NormedSpace.norm_smul_normalize (v m))
    change ⟪K m n (‖u n‖ • a n),‖v m‖ • b m⟫_ℝ = ⟪K m n (u n),v m⟫_ℝ at h
    exact h.symm.trans (hInner (fun k => ‖u k‖) (fun k => ‖v k‖) m n)
  have hWhole : (∑ m ∈ s, ∑ n ∈ s, ((m:ℝ)-(n:ℝ))*G m n*‖u n‖*‖v m‖) =
      ∑ m ∈ s, ∑ n ∈ s, ((m:ℝ)-(n:ℝ))*⟪K m n (u n),v m⟫_ℝ := by
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    calc
      _ = ((m:ℝ)-(n:ℝ))*(G m n*‖u n‖*‖v m‖) := by ring
      _ = _ := congrArg (fun r : ℝ => ((m:ℝ)-(n:ℝ))*r) (hReconstruct m n).symm
  exact (congrArg abs hWhole).symm.trans_le hScalarBound

#print axioms OAI.AnisotropicCalderon.SpectralSylvester.finite_harmonic_weighted_scaled_direction_energy_le
#print axioms OAI.AnisotropicCalderon.SpectralSylvester.finite_harmonic_degree_half_form_bound_of_casimir_product_bound

end OAI.AnisotropicCalderon.SpectralSylvester
