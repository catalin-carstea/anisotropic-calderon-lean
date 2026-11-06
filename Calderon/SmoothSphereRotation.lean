import Calderon.OrthogonalSphereMeasure
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.SmoothSphereRotation
open SphereHarmonic OrthogonalSphereMeasure

/-- The actual coordinate-plane flow, including identity on diagonal pairs. -/
def coordinateRotation (i j : Fin 3) (t : ℝ) (x : R3) : R3 :=
  if i = j then x else WithLp.toLp 2 fun l =>
    if l = i then Real.cos t * x i - Real.sin t * x j else
    if l = j then Real.sin t * x i + Real.cos t * x j else x l

/-- The true ambient generator, with the manuscript's `X_i ∂_j-X_j ∂_i` sign. -/
def rotationVector (i j : Fin 3) (x : R3) : R3 :=
  x i • PiLp.single 2 j (1 : ℝ) - x j • PiLp.single 2 i (1 : ℝ)

def sphereRotationDerivative (i j : Fin 3) (F : R3 → ℝ) (x : R3) : ℝ :=
  fderiv ℝ F x (rotationVector i j x)

lemma rotation_pair_square (t a b : ℝ) :
    (Real.cos t * a - Real.sin t * b)^2 +
      (Real.sin t * a + Real.cos t * b)^2 = a^2 + b^2 := by
  calc
    _ = (Real.sin t ^ 2 + Real.cos t ^ 2) * (a^2 + b^2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

lemma rotation_inverse_first (t a b : ℝ) :
    Real.cos t * (Real.cos t * a + Real.sin t * b) -
      Real.sin t * (-Real.sin t * a + Real.cos t * b) = a := by
  calc
    _ = (Real.sin t ^ 2 + Real.cos t ^ 2) * a := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

lemma rotation_inverse_second (t a b : ℝ) :
    Real.sin t * (Real.cos t * a + Real.sin t * b) +
      Real.cos t * (-Real.sin t * a + Real.cos t * b) = b := by
  calc
    _ = (Real.sin t ^ 2 + Real.cos t ^ 2) * b := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

lemma coordinateRotation_add (i j : Fin 3) (t : ℝ) (x y : R3) :
    coordinateRotation i j t (x+y) = coordinateRotation i j t x +
      coordinateRotation i j t y := by
  ext l
  by_cases hij : i=j
  · simp [coordinateRotation,hij]
  · by_cases hli : l=i <;> by_cases hlj : l=j <;>
      simp [coordinateRotation,hij,Ne.symm hij,hli,hlj] <;> ring

lemma coordinateRotation_smul (i j : Fin 3) (t c : ℝ) (x : R3) :
    coordinateRotation i j t (c • x) = c • coordinateRotation i j t x := by
  ext l
  by_cases hij : i=j
  · simp [coordinateRotation,hij]
  · by_cases hli : l=i <;> by_cases hlj : l=j <;>
      simp [coordinateRotation,hij,Ne.symm hij,hli,hlj] <;> ring

lemma coordinateRotation_inverse (i j : Fin 3) (t : ℝ) (x : R3) :
    coordinateRotation i j t (coordinateRotation i j (-t) x) = x := by
  by_cases hij : i=j
  · simp [coordinateRotation,hij]
  · ext l
    by_cases hli : l=i
    · subst l
      simpa [coordinateRotation,hij,Ne.symm hij,Real.cos_neg,Real.sin_neg] using
        rotation_inverse_first t (x i) (x j)
    · by_cases hlj : l=j
      · subst l
        simpa [coordinateRotation,hij,Ne.symm hij,Real.cos_neg,Real.sin_neg] using
          rotation_inverse_second t (x i) (x j)
      · simp [coordinateRotation,hij,Ne.symm hij,hli,hlj]

lemma coordinateRotation_norm (i j : Fin 3) (t : ℝ) (x : R3) :
    ‖coordinateRotation i j t x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  fin_cases i <;> fin_cases j <;>
    simp [coordinateRotation,Fin.sum_univ_three]
  · nlinarith only [rotation_pair_square t (x 0) (x 1)]
  · nlinarith only [rotation_pair_square t (x 0) (x 2)]
  · nlinarith only [rotation_pair_square t (x 1) (x 0)]
  · nlinarith only [rotation_pair_square t (x 1) (x 2)]
  · nlinarith only [rotation_pair_square t (x 2) (x 0)]
  · nlinarith only [rotation_pair_square t (x 2) (x 1)]

/-- No orthogonality premise is supplied: the trigonometric flow is proved isometric. -/
def coordinateRotationIsometry (i j : Fin 3) (t : ℝ) : R3 ≃ₗᵢ[ℝ] R3 where
  toFun := coordinateRotation i j t
  invFun := coordinateRotation i j (-t)
  left_inv x := by simpa using coordinateRotation_inverse i j (-t) x
  right_inv x := coordinateRotation_inverse i j t x
  map_add' := coordinateRotation_add i j t
  map_smul' c x := coordinateRotation_smul i j t c x
  norm_map' := coordinateRotation_norm i j t

lemma coordinateRotation_zero (i j : Fin 3) (x : R3) :
    coordinateRotation i j 0 x = x := by
  ext l
  by_cases hij : i=j
  · simp [coordinateRotation,hij]
  · by_cases hli : l=i <;> by_cases hlj : l=j <;>
      simp [coordinateRotation,hij,Ne.symm hij,hli,hlj]

lemma rotationVector_self (i : Fin 3) (x : R3) : rotationVector i i x = 0 := by
  simp [rotationVector]

lemma contDiff_coordinateRotation (i j : Fin 3) :
    ContDiff ℝ ∞ (fun q : ℝ × R3 => coordinateRotation i j q.1 q.2) := by
  apply contDiff_piLp'
  intro l
  by_cases hij : i=j
  · simp only [coordinateRotation,ite_eq_left hij]
    fun_prop
  · by_cases hli : l=i <;> by_cases hlj : l=j <;>
      simp only [coordinateRotation,ite_eq_right hij,Ne.symm hij,PiLp.toLp_apply,hli,hlj,ite_true,ite_false] <;> fun_prop

lemma continuous_sphereCoordinateRotation (i j : Fin 3) :
    Continuous (fun q : ℝ × UnitSphere => coordinateRotation i j q.1 q.2.val) := by
  have h1 : Continuous (fun q : ℝ × R3 => coordinateRotation i j q.1 q.2) :=
    (contDiff_coordinateRotation i j).continuous
  have h2 : Continuous (fun q : ℝ × UnitSphere => (q.1,q.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  convert! h1.comp h2 using 1

lemma contDiff_rotationVector (i j : Fin 3) : ContDiff ℝ ∞ (rotationVector i j) := by
  unfold rotationVector
  fun_prop

lemma contDiff_sphereRotationDerivative (i j : Fin 3) (F : R3 → ℝ)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (sphereRotationDerivative i j F) := by
  exact (contDiff_infty_iff_fderiv.mp hF).2.clm_apply (contDiff_rotationVector i j)

lemma hasDerivAt_coordinateRotation (i j : Fin 3) (t : ℝ) (x : R3) :
    HasDerivAt (fun s => coordinateRotation i j s x)
      (rotationVector i j (coordinateRotation i j t x)) t := by
  have hpi : HasDerivAt (fun s => fun l => coordinateRotation i j s x l)
      (fun l => rotationVector i j (coordinateRotation i j t x) l) t := by
    apply hasDerivAt_pi.mpr
    intro l
    by_cases hij : i=j
    · simpa [coordinateRotation,hij,rotationVector] using hasDerivAt_const t (x l)
    · by_cases hli : l=i
      · subst l
        convert ((Real.hasDerivAt_cos t).mul_const (x i)).sub
          ((Real.hasDerivAt_sin t).mul_const (x j)) using 1 <;>
          simp [coordinateRotation,rotationVector,hij,Ne.symm hij,funext_iff,Pi.sub_apply,Pi.add_apply,mul_comm] <;> ring
      · by_cases hlj : l=j
        · subst l
          convert ((Real.hasDerivAt_sin t).mul_const (x i)).add
            ((Real.hasDerivAt_cos t).mul_const (x j)) using 1 <;>
            simp [coordinateRotation,rotationVector,hij,Ne.symm hij,funext_iff,Pi.sub_apply,Pi.add_apply,mul_comm] <;> ring
        · simpa [coordinateRotation,rotationVector,hij,Ne.symm hij,hli,hlj,Ne.symm hli,Ne.symm hlj]
            using hasDerivAt_const t (x l)
  convert!
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t hpi using 1 <;> rfl

lemma hasDerivAt_rotation_comp (i j : Fin 3) (F : R3 → ℝ)
    (hF : ContDiff ℝ ∞ F) (t : ℝ) (x : R3) :
    HasDerivAt (fun s => F (coordinateRotation i j s x))
      (sphereRotationDerivative i j F (coordinateRotation i j t x)) t := by
  exact ((hF.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_coordinateRotation i j t x)

lemma integrable_sphere_continuous (f : UnitSphere → ℝ) (hf : Continuous f) :
    Integrable f sphereProbability := by
  have hi := hf.continuousOn.integrableOn_of_subset_isCompact isCompact_univ
    MeasurableSet.univ (show (univ : Set UnitSphere) ⊆ univ from Subset.rfl)
    (show sphereProbability univ ≠ (⊤ : ℝ≥0∞) by simp)
  simpa only [IntegrableOn,Measure.restrict_univ] using hi

lemma integral_rotation_product (i j : Fin 3) (t : ℝ) (F G : R3 → ℝ) :
    (∫ u : UnitSphere, F (coordinateRotation i j t u.val) *
      G (coordinateRotation i j t u.val) ∂sphereProbability) =
    ∫ u : UnitSphere, F u.val * G u.val ∂sphereProbability := by
  exact (orthogonalSphereHomeomorph_sphereProbability_preserving
    (coordinateRotationIsometry i j t)).integral_comp
      (orthogonalSphereHomeomorph (coordinateRotationIsometry i j t)).measurableEmbedding
      (fun u : UnitSphere => F u.val * G u.val)

/-- The uniform bound is derived on one compact product before any orbit integral derivative. -/
lemma exists_rotation_product_derivative_bound (i j : Fin 3) (F G : R3 → ℝ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (-1 : ℝ) 1, ∀ u : UnitSphere,
      ‖sphereRotationDerivative i j F (coordinateRotation i j t u.val) *
        G (coordinateRotation i j t u.val) + F (coordinateRotation i j t u.val) *
        sphereRotationDerivative i j G (coordinateRotation i j t u.val)‖ ≤ C := by
  let D : ℝ × UnitSphere → ℝ := fun q =>
    sphereRotationDerivative i j F (coordinateRotation i j q.1 q.2.val) *
      G (coordinateRotation i j q.1 q.2.val) +
    F (coordinateRotation i j q.1 q.2.val) *
      sphereRotationDerivative i j G (coordinateRotation i j q.1 q.2.val)
  have hrot : Continuous (fun q : ℝ × UnitSphere => coordinateRotation i j q.1 q.2.val) :=
    continuous_sphereCoordinateRotation i j
  have hD : Continuous D := by
    exact (((contDiff_sphereRotationDerivative i j F hF).continuous.comp hrot).mul
      (hG.continuous.comp hrot)).add
      ((hF.continuous.comp hrot).mul
        ((contDiff_sphereRotationDerivative i j G hG).continuous.comp hrot))
  have hK : IsCompact (Icc (-1 : ℝ) 1 ×ˢ (univ : Set UnitSphere)) :=
    isCompact_Icc.prod isCompact_univ
  rcases hK.bddAbove_image hD.norm.continuousOn with ⟨C,hC⟩
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro t ht u
  exact (hC (mem_image_of_mem _ (show (t,u) ∈ Icc (-1 : ℝ) 1 ×ˢ
    (univ : Set UnitSphere) from ⟨ht,mem_univ _⟩))).trans (le_max_left _ _)

/-- Actual weak skew-adjunction for the sphere probability measure and true rotation fields. -/
theorem integral_sphereRotationDerivative_skew (i j : Fin 3) (F G : R3 → ℝ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    (∫ u : UnitSphere, sphereRotationDerivative i j F u.val * G u.val ∂sphereProbability) =
      -(∫ u : UnitSphere, F u.val * sphereRotationDerivative i j G u.val ∂sphereProbability) := by
  let H : ℝ → UnitSphere → ℝ := fun t u =>
    F (coordinateRotation i j t u.val) * G (coordinateRotation i j t u.val)
  let D : ℝ → UnitSphere → ℝ := fun t u =>
    sphereRotationDerivative i j F (coordinateRotation i j t u.val) *
      G (coordinateRotation i j t u.val) +
    F (coordinateRotation i j t u.val) *
      sphereRotationDerivative i j G (coordinateRotation i j t u.val)
  have hrot (t : ℝ) : Continuous (fun u : UnitSphere => coordinateRotation i j t u.val) :=
    (coordinateRotationIsometry i j t).continuous.comp continuous_subtype_val
  have hH (t : ℝ) : Continuous (H t) :=
    (hF.continuous.comp (hrot t)).mul (hG.continuous.comp (hrot t))
  have hD (t : ℝ) : Continuous (D t) :=
    (((contDiff_sphereRotationDerivative i j F hF).continuous.comp (hrot t)).mul
      (hG.continuous.comp (hrot t))).add
      ((hF.continuous.comp (hrot t)).mul
        ((contDiff_sphereRotationDerivative i j G hG).continuous.comp (hrot t)))
  obtain ⟨C,hC,hbound⟩ := exists_rotation_product_derivative_bound i j F G hF hG
  have hdiff : ∀ u : UnitSphere, ∀ t : ℝ, HasDerivAt (fun s => H s u) (D t u) t := by
    intro u t
    exact (hasDerivAt_rotation_comp i j F hF t u.val).mul
      (hasDerivAt_rotation_comp i j G hG t u.val)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := H) (F' := D) (μ := sphereProbability) (x₀ := (0 : ℝ))
    (s := Ioo (-1 : ℝ) 1) (bound := fun _ : UnitSphere => C)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => (hH t).aestronglyMeasurable)
    (integrable_sphere_continuous (H 0) (hH 0))
    ((hD 0).aestronglyMeasurable)
    (Eventually.of_forall fun u t ht => hbound t ⟨le_of_lt ht.1,le_of_lt ht.2⟩ u)
    (integrable_const C)
    (Eventually.of_forall fun u t _ => hdiff u t)).2
  have hconst : (fun t => ∫ u : UnitSphere, H t u ∂sphereProbability) =
      fun _ : ℝ => ∫ u : UnitSphere, F u.val * G u.val ∂sphereProbability := by
    funext t
    exact integral_rotation_product i j t F G
  have hz : (∫ u : UnitSphere, D 0 u ∂sphereProbability) = 0 :=
    hd.unique (by
      rw [hconst]
      exact hasDerivAt_const (0 : ℝ)
        (∫ u : UnitSphere, F u.val * G u.val ∂sphereProbability))
  have hleft := integrable_sphere_continuous
    (fun u : UnitSphere => sphereRotationDerivative i j F u.val * G u.val)
    (((contDiff_sphereRotationDerivative i j F hF).continuous.comp continuous_subtype_val).mul
      (hG.continuous.comp continuous_subtype_val))
  have hright := integrable_sphere_continuous
    (fun u : UnitSphere => F u.val * sphereRotationDerivative i j G u.val)
    ((hF.continuous.comp continuous_subtype_val).mul
      ((contDiff_sphereRotationDerivative i j G hG).continuous.comp continuous_subtype_val))
  simp only [D,coordinateRotation_zero] at hz
  rw [integral_add hleft hright] at hz
  linarith

lemma sphereRotationDerivative_eq_zero_of_sphere_zero (i j : Fin 3) (F : R3 → ℝ)
    (hF : ContDiff ℝ ∞ F) (hzero : ∀ u : UnitSphere, F u.val = 0) (u : UnitSphere) :
    sphereRotationDerivative i j F u.val = 0 := by
  have hz : (fun t : ℝ => F (coordinateRotation i j t u.val)) = fun _ : ℝ => 0 := by
    funext t
    exact hzero (orthogonalSphereHomeomorph (coordinateRotationIsometry i j t) u)
  have hd := hasDerivAt_rotation_comp i j F hF 0 u.val
  simp only [coordinateRotation_zero] at hd
  exact hd.unique (by rw [hz]; exact hasDerivAt_const (0 : ℝ) (0 : ℝ))

end OAI.AnisotropicCalderon.SmoothSphereRotation
