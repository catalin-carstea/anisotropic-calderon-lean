import Calderon.ActualHigherSPrincipalPhysicalForms
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualWeightedHorizontalActionBounds
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ReferenceDensityBounds ConformalDepth RadiusProfile ActualAngularPiDraft
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "BH" => (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highModule : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] highNormed highModule

private lemma compact_family_bound {α E ι : Type*} [TopologicalSpace α]
    [NormedAddCommGroup E] [Fintype ι] (K : Set α) (hK : IsCompact K)
    (f : ι → α → E) (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i, ∀ x ∈ K, ‖f i x‖ ≤ C := by
  classical
  have hi (i : ι) : ∃ C : ℝ, ∀ x ∈ K, ‖f i x‖ ≤ C :=
    hK.exists_bound_of_continuousOn (hf i)
  choose C hC using hi
  refine ⟨1+∑ i, |C i|,le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => abs_nonneg (C i))),?_⟩
  intro i x hx
  exact (hC i x hx).trans ((le_abs_self _).trans (by
    have h := Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ i)
    linarith))

private lemma norm_three_terms_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b c : E) (f : ℝ) : ‖a+b+f • c‖ ≤ (‖a‖+‖b‖)+|f| * ‖c‖ := by
  simpa only [norm_smul,Real.norm_eq_abs] using
    (norm_add_le (a+b) (f • c)).trans (add_le_add (norm_add_le a b) (le_refl ‖f • c‖))

/-- Actual fixed native connection cap, from scalar coefficients and fixed rotation norms. -/
lemma norm_high_horizontal_angular_le (g : MatrixField) (L q : ℝ) (x : R3) (i : Fin 3)
    (M : ℝ) (hM : 0 ≤ M)
    (hΓ : ∀ a b : Fin 3, |referenceFrameConnectionCoefficient g L q x
      (referenceMetricGramFrame g L (q,x) i) a b| ≤ M) :
    ‖referenceHighHorizontalAngularL g L q x i‖ ≤
      (1/2 : ℝ)*M*(∑ a : Fin 3, ∑ b : Fin 3, ‖sphereSobolevRotationL (3/2 : ℝ) a b‖) := by
  unfold referenceHighHorizontalAngularL
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  calc
    _ ≤ (1/2 : ℝ)*(∑ a : Fin 3, ∑ b : Fin 3,
      |referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) a b| *
        ‖sphereSobolevRotationL (3/2 : ℝ) a b‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ =>
        (norm_sum_le _ _).trans (by simp only [norm_smul,Real.norm_eq_abs];rfl)))
    _ ≤ (1/2 : ℝ)*(∑ a : Fin 3, ∑ b : Fin 3, M*‖sphereSobolevRotationL (3/2 : ℝ) a b‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ =>
        mul_le_mul_of_nonneg_right (hΓ a b) (norm_nonneg _)))
    _ = _ := by simp only [← Finset.mul_sum];ring

/-- Constants before all original profiles and all high-valued inputs. -/
theorem exists_weighted_horizontal_uniform_bound (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δr Ar : ℝ, ∀ p : ℕ,
      0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p → ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ K,
      1 ≤ ReferenceWeightedApproximation.actualReferenceBeta g L q δr Ar p x →
      ∀ u : R3 → Hi, ∀ i : Fin 3,
      ‖referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) u x i‖ ≤
        ‖IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i))‖ +
        C*ReferenceWeightedApproximation.actualReferenceBeta g L q δr Ar p x*‖u x‖ := by
  obtain ⟨M,hM,hGeo⟩ := ActualHorizontalNormBridge.exists_reference_geometry_uniform_bounds g hg L K hK
  obtain ⟨CX,hCX,hFrame⟩ := compact_family_bound (Icc (0 : ℝ) 1 ×ˢ K) (isCompact_Icc.prod hK)
    (fun i : Fin 3 => fun t : ℝ × R3 => referenceMetricGramFrame g L t i)
    (fun i => (contDiff_referenceMetricGramFrame g hg L i).continuous.continuousOn)
  obtain ⟨J1,J2,hJ1,_hJ2,hLog⟩ := exists_dilated_referenceRadius_uniform_first_second_jet_bounds_at
    g hg K hK L hL
  let CO := (1/2 : ℝ)*M*(∑ a : Fin 3, ∑ b : Fin 3, ‖sphereSobolevRotationL (3/2 : ℝ) a b‖)
  let Cf := J1*CX
  let C := CO+Cf*‖BH‖
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hCX0 : 0 ≤ CX := zero_le_one.trans hCX
  have hCO : 0 ≤ CO := by dsimp only [CO];positivity
  have hCf : 0 ≤ Cf := mul_nonneg hJ1.le hCX0
  refine ⟨C,add_nonneg hCO (mul_nonneg hCf (norm_nonneg _)),?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq x hx hβ u i
  let β := ReferenceWeightedApproximation.actualReferenceBeta g L q δr Ar p x
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ
  have hΓ := (hGeo q hq x hx).2.2.2 i
  have hO : ‖referenceHighHorizontalAngularL g L q x i‖ ≤ CO :=
    norm_high_horizontal_angular_le g L q x i M hM0 hΓ
  have hX : ‖referenceMetricGramFrame g L (q,x) i‖ ≤ CX := hFrame i (q,x) ⟨hq,hx⟩
  have hf : |referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i| ≤ Cf*β := by
    have he : referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i =
        fderiv ℝ (fun y => Real.log (referenceRadius δr Ar p L y)) x
          (referenceMetricGramFrame g L (q,x) i) := by
      unfold referenceRadiusHorizontalLogDerivative
      rw [ActualHigherSZeroCoefficientBounds.conformalFrame_coordinateVector_eq g L q x i]
    rw [he,← Real.norm_eq_abs]
    calc
      _ ≤ ‖fderiv ℝ (fun y => Real.log (referenceRadius δr Ar p L y)) x‖*
          ‖referenceMetricGramFrame g L (q,x) i‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (J1*β)*CX := mul_le_mul (hLog q hq δr hδr hδr1 Ar hAr p hp x hx).1
        hX (norm_nonneg _) (mul_nonneg hJ1.le hβ0)
      _ = Cf*β := by dsimp only [Cf];ring
  have hConn : ‖referenceHighHorizontalAngularL g L q x i (u x)‖ ≤ CO*‖u x‖ :=
    ((referenceHighHorizontalAngularL g L q x i).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hO (norm_nonneg _))
  have hB : |referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i| *‖BH (u x)‖ ≤
      (Cf*β)*(‖BH‖*‖u x‖) :=
    mul_le_mul hf (ContinuousLinearMap.le_opNorm BH _) (norm_nonneg _) (mul_nonneg hCf hβ0)
  have hCOβ : CO*‖u x‖ ≤ CO*β*‖u x‖ :=
    mul_le_mul_of_nonneg_right (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ hCO) (norm_nonneg _)
  change ‖(IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i))+
      referenceHighHorizontalAngularL g L q x i (u x))+
      referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i • BH (u x)‖ ≤ _
  have hRaw := norm_three_terms_le
    (IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i)))
    (referenceHighHorizontalAngularL g L q x i (u x)) (BH (u x))
    (referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i)
  refine hRaw.trans ?_
  calc
    _ ≤ (‖IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i))‖+CO*‖u x‖)+
        (Cf*β)*(‖BH‖*‖u x‖) := add_le_add (add_le_add (le_refl _) hConn) hB
    _ ≤ (‖IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i))‖+CO*β*‖u x‖)+
        (Cf*β)*(‖BH‖*‖u x‖) := add_le_add (add_le_add (le_refl _) hCOβ) (le_refl _)
    _ = _ := by dsimp only [C] <;> ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualWeightedHorizontalActionBounds
