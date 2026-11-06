import Calderon.ActualNormalizedSecondMixedCommutatorForm

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualNormalizedSecondMixedWeakPairing
open SphereHarmonic SphereHilbertDecomposition SpectralWeightedGraph
  SmoothSphereFields SmoothAngularApplication SmoothMetricFrame ReferenceDensityBounds
  PrincipalCommutator BaseDensityAdjoint ActualPhysicalMixedFirst
  ActualNormalizedSecondModelErrorAssembly ActualAngularDerivativeRaisingCommutator
  ActualAngularCommutatorHalfForm ActualReferenceDDSpectralTransport
  ActualNormalizedSecondMixedCommutatorForm SectionFiveErrorForms

lemma directional_constantAngular (A : SphereL2 →L[ℝ] SphereL2) (X : R3)
    (u : R3 → SphereL2) (hu : ContDiff ℝ ∞ u) (x : R3) :
    directionalDeriv X (fun y => A (u y)) x = A (directionalDeriv X u x) := by
  have h := directionalFDeriv_clm_apply X (fun _ : R3 => A) u contDiff_const hu x
  simpa only [directionalFDeriv,directionalDeriv,fderiv_const_apply,
    ContinuousLinearMap.zero_apply,zero_add] using h

/-- One actual compact base integration retains the derivative of the whole weight. -/
theorem compact_constantAngular_second_pairing
    (A : SphereL2 →L[ℝ] SphereL2) (X Y : R3)
    (w : R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (u : R3 → SphereL2) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    (∫ x, w x*⟪A (directionalDeriv X (directionalDeriv Y u) x),u x⟫_ℝ) =
      -(∫ x, w x*⟪A (directionalDeriv Y u x),directionalDeriv X u x⟫_ℝ) -
      (∫ x, directionalDeriv X w x*⟪A (directionalDeriv Y u x),u x⟫_ℝ) := by
  have hX := BaseDensityAdjoint.contDiff_directionalDeriv X u hu
  have hY := BaseDensityAdjoint.contDiff_directionalDeriv Y u hu
  have hcY := BaseDensityAdjoint.hasCompactSupport_directionalDeriv Y u hc
  have hAu : ContDiff ℝ ∞ (fun x => A (directionalDeriv Y u x)) := A.contDiff.comp hY
  have hcAu : HasCompactSupport (fun x => A (directionalDeriv Y u x)) := hcY.comp_left (map_zero A)
  have hPrin : Integrable (fun x => w x*⟪A (directionalDeriv Y u x),directionalDeriv X u x⟫_ℝ) := by
    have h := BaseDensityAdjoint.compact_inner_integrable
      (fun x => w x • directionalDeriv X u x) (fun x => A (directionalDeriv Y u x))
      (hw.smul hX).continuous hAu.continuous hcAu
    simpa only [real_inner_smul_left,real_inner_comm] using h
  have hRem : Integrable (fun x => directionalDeriv X w x*⟪A (directionalDeriv Y u x),u x⟫_ℝ) := by
    have h := BaseDensityAdjoint.compact_inner_integrable
      (fun x => directionalDeriv X w x • u x) (fun x => A (directionalDeriv Y u x))
      ((BaseDensityAdjoint.contDiff_directionalDeriv X w hw).smul hu).continuous hAu.continuous hcAu
    simpa only [real_inner_smul_left,real_inner_comm] using h
  have hIbp := BaseDensityAdjoint.compact_inner_directionalDeriv X
    (fun x => w x • u x) (fun x => A (directionalDeriv Y u x)) (hw.smul hu) hAu hcAu
  calc
    _ = ∫ x, ⟪w x • u x,directionalDeriv X (fun y => A (directionalDeriv Y u y)) x⟫_ℝ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only
        rw [directional_constantAngular A X _ hY x,real_inner_smul_left,real_inner_comm])
    _ = -(∫ x, ⟪directionalDeriv X (fun y => w y • u y) x,A (directionalDeriv Y u x)⟫_ℝ) := hIbp
    _ = -(∫ x, directionalDeriv X w x*⟪A (directionalDeriv Y u x),u x⟫_ℝ+
        w x*⟪A (directionalDeriv Y u x),directionalDeriv X u x⟫_ℝ) := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only
        rw [BaseDensityAdjoint.directionalDeriv_smul X w u hw hu x]
        simp only [inner_add_left,real_inner_smul_left,real_inner_comm])
    _ = -((∫ x, directionalDeriv X w x*⟪A (directionalDeriv Y u x),u x⟫_ℝ)+
        (∫ x, w x*⟪A (directionalDeriv Y u x),directionalDeriv X u x⟫_ℝ)) := by
      congr 1
      simpa only [Pi.add_apply] using integral_add hRem hPrin
    _ = _ := by ring

lemma contDiff_mixedSecondWordCoefficient
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (i j a b : Fin 3) :
    ContDiff ℝ ∞ (mixedSecondWordCoefficient g1 g2 L lam i j a b) := by
  have he (a i : Fin 3) : ContDiff ℝ ∞ (fun x => referenceMetricGramFrame g1 L (lam,x) a i) :=
    (contDiff_piLp_apply (p := 2) (i := i) : ContDiff ℝ ∞ (fun v : R3 => v i)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a)
  have hm (a i : Fin 3) : ContDiff ℝ ∞ (physicalMixedFirstCoefficient g1 L lam
      (NormalizedPrincipalMetric.referenceNormalizedPrincipalDifference g1 g2 L lam) a i) :=
    contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
      (fun i j => NormalizedPrincipalMetricSmooth.contDiff_referenceNormalizedPrincipalDifference_entry
        g1 g2 hg1 hg2 L lam i j) a i
  unfold mixedSecondWordCoefficient
  exact (((contDiff_const.mul (he a i)).add (hm a i)).mul (hm b j)).add
    ((contDiff_const.mul (hm a i)).mul (he b j))

/-- Full two-base native graph transport; no raw angular operator is bounded. -/
theorem normalizedCommutator_second_inner_half_identity
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (a b i j : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ⟪normalizedDerivativeRaisingCommutator hF hO hD a b
      (directionalDeriv (coordinateDirection i) (directionalDeriv (coordinateDirection j)
        (ambientBesselField hO hD 1 (by norm_num) G hG)) x),ambientSphereL2 G hG x⟫_ℝ =
    ⟪normalizedDerivativeRaisingCommutator hF hO hD a b
      (directionalDeriv (coordinateDirection i) (directionalDeriv (coordinateDirection j)
        (ambientBesselField hO hD (1/2) (by norm_num) G hG)) x),
      ambientBesselField hO hD (1/2) (by norm_num) G hG x⟫_ℝ := by
  have hj :
      (directionalDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x,
        directionalDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x) ∈
      sphereBesselGraph hO hD (1/2) := by
    convert directional_ambientBesselField_between_graph hO hD (1/2) 1
      (by norm_num) (by norm_num) G hG x (coordinateDirection j) using 1 <;> norm_num [BaseDensityAdjoint.directionalDeriv, PrincipalCommutator.directionalFDeriv]
  have hij := directionalDeriv_besselGraph hO hD (1/2) (coordinateDirection i)
    (directionalDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG))
    (directionalDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG))
    (BaseDensityAdjoint.contDiff_directionalDeriv _ _ (contDiff_ambientBesselField hO hD (1/2) (by norm_num) G hG))
    (BaseDensityAdjoint.contDiff_directionalDeriv _ _ (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG))
    (fun x => by
      convert directional_ambientBesselField_between_graph hO hD (1/2) 1
        (by norm_num) (by norm_num) G hG x (coordinateDirection j) using 1 <;> norm_num [BaseDensityAdjoint.directionalDeriv, PrincipalCommutator.directionalFDeriv]) x
  exact spectralGraph_inner_symm hO hD (besselWeight (1/2)) _ _ _ _
    (preservesSphereSpectralGraphs_normalizedDerivativeRaisingCommutator hF hO hD a b _ _ _ hij)
    (ambientBesselField_graph hO hD (1/2) (by norm_num) G hG x)

/-- The literal actual mixed word, including the full differentiated mu*c remainder. -/
theorem compact_mixedSecondWord_raw_second_pairing
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (i j a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    (∫ x, referenceDensityFamily g1 L (lam,x)*mixedSecondWordCoefficient g1 g2 L lam i j a b x *
      ⟪normalizedDerivativeRaisingCommutator hF hO hD a b
        (directionalDeriv (coordinateDirection i) (directionalDeriv (coordinateDirection j)
          (ambientBesselField hO hD 1 (by norm_num) G hG)) x),ambientSphereL2 G hG x⟫_ℝ) =
    -(∫ x, referenceDensityFamily g1 L (lam,x)*mixedSecondWordCoefficient g1 g2 L lam i j a b x *
      ⟪normalizedDerivativeRaisingCommutator hF hO hD a b
        (directionalDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x),
        directionalDeriv (coordinateDirection i) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x⟫_ℝ) -
    (∫ x, directionalDeriv (coordinateDirection i)
      (fun y => referenceDensityFamily g1 L (lam,y)*mixedSecondWordCoefficient g1 g2 L lam i j a b y) x *
      ⟪normalizedDerivativeRaisingCommutator hF hO hD a b
        (directionalDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x),
        ambientBesselField hO hD (1/2) (by norm_num) G hG x⟫_ℝ) := by
  have hmu : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g1 L (lam,x)) :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hc := contDiff_mixedSecondWordCoefficient g1 g2 hg1 hg2 L lam i j a b
  calc
    _ = ∫ x, referenceDensityFamily g1 L (lam,x)*mixedSecondWordCoefficient g1 g2 L lam i j a b x *
        ⟪normalizedDerivativeRaisingCommutator hF hO hD a b
          (directionalDeriv (coordinateDirection i) (directionalDeriv (coordinateDirection j)
            (ambientBesselField hO hD (1/2) (by norm_num) G hG)) x),
          ambientBesselField hO hD (1/2) (by norm_num) G hG x⟫_ℝ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => congrArg
        (fun t : ℝ => referenceDensityFamily g1 L (lam,x)*mixedSecondWordCoefficient g1 g2 L lam i j a b x*t)
        (normalizedCommutator_second_inner_half_identity hF hO hD a b i j G hG x))
    _ = _ := compact_constantAngular_second_pairing
      (normalizedDerivativeRaisingCommutator hF hO hD a b)
      (coordinateDirection i) (coordinateDirection j)
      (fun x => referenceDensityFamily g1 L (lam,x)*mixedSecondWordCoefficient g1 g2 L lam i j a b x)
      (hmu.mul hc) (ambientBesselField hO hD (1/2) (by norm_num) G hG)
      (contDiff_ambientBesselField hO hD (1/2) (by norm_num) G hG)
      (hasCompactSupport_ambientBesselField hO hD (1/2) (by norm_num) G hG K hK hz)

end OAI.AnisotropicCalderon.ActualNormalizedSecondMixedWeakPairing
