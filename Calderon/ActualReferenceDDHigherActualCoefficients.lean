import Calderon.ActualReferenceDDHigherCLMProducts
import Calderon.ActualReferenceDDHigherLogFrameJets
import Calderon.ActualReferenceDDHigherSpectralGraphs
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualReferenceDDHigherActualCoefficients
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  BoundedAngularShift ActualScalarPrincipalAdjoint
  SmoothMetricFrame MovingFrameConnection AmbientReferenceRaising AmbientReferenceCovariantCore
  ActualHorizontalNormBridge ActualReferenceParallelRaising ActualReferenceModelTrace
  ActualReferenceScaledRaisingTransport ActualReferenceDDNormalizedCoefficient ActualReferenceDDGeometryBounds
  ActualReferenceDDCoefficientSmallness ActualReferenceDDSpectralTransport
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets
  ActualReferenceDDHigherProfileJets ActualReferenceDDHigherLogFrameJets
  ActualReferenceDDHigherSpectralGraphs ActualReferenceDDHigherCLMProducts
  ActualPhysicalMixedReferenceCancellation ActualPhysicalMixedNative
  ReferenceDensityBounds MetricOperator CoordinateBootstrapJets
  PrincipalCommutator ConformalDepth RadiusProfile PerturbedDensityAdjoint

def zeroBaseJetConstant (N : ℕ) (M F : ℝ) : ℝ :=
  M+2*(2:ℝ)^N*F

def firstBaseJetConstant (N : ℕ) (M F : ℝ) : ℝ :=
  (2:ℝ)^N*M+2*(2:ℝ)^N*M^2+4*((2:ℝ)^N)^2*F*M

def secondBaseJetConstant (N : ℕ) (M F : ℝ) : ℝ :=
  (2:ℝ)^N*M+2*(2:ℝ)^N*F+(2:ℝ)^N*M*zeroBaseJetConstant N M F+3*((2:ℝ)^N)^2*M*zeroBaseJetConstant N M F+(2:ℝ)^N*F*(zeroBaseJetConstant N M F+(2:ℝ)^N*zeroBaseJetConstant N M F)

lemma zeroBaseJetConstant_nonneg (N : ℕ) (M F : ℝ) (hM : 0 ≤ M) (hF : 0 ≤ F) :
    0 ≤ zeroBaseJetConstant N M F := by
  unfold zeroBaseJetConstant
  positivity

lemma firstBaseJetConstant_nonneg (N : ℕ) (M F : ℝ) (hM : 0 ≤ M) (hF : 0 ≤ F) :
    0 ≤ firstBaseJetConstant N M F := by
  unfold firstBaseJetConstant
  positivity

lemma secondBaseJetConstant_nonneg (N : ℕ) (M F : ℝ) (hM : 0 ≤ M) (hF : 0 ≤ F) :
    0 ≤ secondBaseJetConstant N M F := by
  unfold secondBaseJetConstant zeroBaseJetConstant
  positivity

lemma hasCoordinateWordJetBound_referenceWeightedZeroBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (N : ℕ) (x : R3) (M F beta : ℝ)
    (hM : 0 ≤ M) (hF : 0 ≤ F) (hb : 1 ≤ beta)
    (hK : ∀ a, HasCoordinateWordJetBound N
      (fun y => normalizedReferenceAngularConnection hO hD g L lam y
        (referenceMetricGramFrame g L (lam,y) a)) x M beta 0)
    (hf : ∀ a, HasCoordinateWordJetBound N
      (referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)))
      x F beta 1)
    (a : Fin 3) :
    HasCoordinateWordJetBound N
      (referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a)
      x (zeroBaseJetConstant N M F) beta 1 := by
  have hb0 : 0 ≤ beta := by linarith
  let Ka : R3 → SphereL2 →L[ℝ] SphereL2 := fun y =>
    normalizedReferenceAngularConnection hO hD g L lam y (referenceMetricGramFrame g L (lam,y) a)
  let fa : R3 → ℝ := referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y))
  let IminusD : SphereL2 →L[ℝ] SphereL2 := ContinuousLinearMap.id ℝ SphereL2-inverseDegreeMultiplier hO hD
  have hKaS : ContDiff ℝ ∞ Ka := contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam a
  have hfaS : ContDiff ℝ ∞ fa := contDiff_referenceFrameDerivative g hg L lam a _
    (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have hKa := hasCoordinateWordJetBound_raise_degree N Ka x M beta 0 1 hM hb (by omega) (hK a)
  have hConstant : HasCoordinateWordJetBound N (fun _ : R3 => IminusD) x 2 beta 0 :=
    hasCoordinateWordJetBound_const_normed N IminusD x 2 beta
      (norm_id_sub_inverseDegreeMultiplier_le_two hO hD) hb0
  have hTerm := hasCoordinateWordJetBound_smul N fa (fun _ : R3 => IminusD) hfaS contDiff_const
    x F 2 beta 1 0 hF (by norm_num) hb0 (hf a) hConstant
  have hSum := hasCoordinateWordJetBound_add N Ka (fun y => fa y • IminusD)
    hKaS (hfaS.smul contDiff_const) x M ((2:ℝ)^N*F*2) beta 1 hKa hTerm
  have he : M+(2:ℝ)^N*F*2=zeroBaseJetConstant N M F := by unfold zeroBaseJetConstant; ring
  rw [he] at hSum
  exact hSum

lemma hasCoordinateWordJetBound_referenceCovectorFirstBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (N : ℕ) (x : R3) (M F beta : ℝ)
    (hM : 0 ≤ M) (hF : 0 ≤ F) (hb : 1 ≤ beta)
    (hE : ∀ a j, HasCoordinateWordJetBound N
      (fun y => referenceMetricGramFrame g L (lam,y) a j) x M beta 0)
    (hGamma : ∀ a b j, HasCoordinateWordJetBound N
      (fun y => referenceConnectionFamily g L (lam,y) (referenceMetricGramFrame g L (lam,y) a)
        (referenceMetricGramFrame g L (lam,y) b) j) x M beta 0)
    (hK : ∀ a, HasCoordinateWordJetBound N
      (fun y => normalizedReferenceAngularConnection hO hD g L lam y
        (referenceMetricGramFrame g L (lam,y) a)) x M beta 0)
    (hf : ∀ a, HasCoordinateWordJetBound N
      (referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)))
      x F beta 1)
    (a b j : Fin 3) :
    HasCoordinateWordJetBound N
      (referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p a b j)
      x (firstBaseJetConstant N M F) beta 1 := by
  have hb0 : 0 ≤ beta := by linarith
  let T : ℝ := (2:ℝ)^N
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  let Ea : R3 → ℝ := fun y => referenceMetricGramFrame g L (lam,y) a j
  let Eb : R3 → ℝ := fun y => referenceMetricGramFrame g L (lam,y) b j
  let Gamma : R3 → ℝ := fun y => referenceConnectionFamily g L (lam,y)
    (referenceMetricGramFrame g L (lam,y) a) (referenceMetricGramFrame g L (lam,y) b) j
  let Kc : Fin 3 → R3 → SphereL2 →L[ℝ] SphereL2 := fun c y =>
    normalizedReferenceAngularConnection hO hD g L lam y (referenceMetricGramFrame g L (lam,y) c)
  let fc : Fin 3 → R3 → ℝ := fun c => referenceFrameDerivative g L lam c
    (fun y => Real.log (referenceRadius δ R p L y))
  let D : SphereL2 →L[ℝ] SphereL2 := inverseDegreeMultiplier hO hD
  let IminusD : SphereL2 →L[ℝ] SphereL2 := ContinuousLinearMap.id ℝ SphereL2-D
  have hES (c : Fin 3) : ContDiff ℝ ∞ (fun y => referenceMetricGramFrame g L (lam,y) c j) :=
    (contDiff_piLp_apply (p := 2) (i := j)).comp (contDiff_referenceMetricGramFrame_slice g hg L lam c)
  have hGammaS : ContDiff ℝ ∞ Gamma := (contDiff_referenceDDGammaFrameEntryJoint g hg L a b j).comp
    (contDiff_const.prodMk contDiff_id)
  have hKS (c : Fin 3) : ContDiff ℝ ∞ (Kc c) := contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam c
  have hfS (c : Fin 3) : ContDiff ℝ ∞ (fc c) := contDiff_referenceFrameDerivative g hg L lam c _
    (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have hDjet : HasCoordinateWordJetBound N (fun _ : R3 => D) x 1 beta 0 :=
    hasCoordinateWordJetBound_const_normed N D x 1 beta (norm_inverseDegreeMultiplier_le_one hO hD) hb0
  have hIDjet : HasCoordinateWordJetBound N (fun _ : R3 => IminusD) x 2 beta 0 :=
    hasCoordinateWordJetBound_const_normed N IminusD x 2 beta (norm_id_sub_inverseDegreeMultiplier_le_two hO hD) hb0
  have hNegGamma := hasCoordinateWordJetBound_neg N Gamma hGammaS x M beta 0 (hGamma a b j)
  have hTerm0 : HasCoordinateWordJetBound N (fun y => -Gamma y • D) x (T*M) beta 0 := by
    have ht := hasCoordinateWordJetBound_smul N (fun y => -Gamma y) (fun _ : R3 => D)
      hGammaS.neg contDiff_const x M 1 beta 0 0 hM (by norm_num) hb0 hNegGamma hDjet
    simpa only [T,mul_one,Nat.zero_add] using ht
  have hTerm0' := hasCoordinateWordJetBound_raise_degree N (fun y => -Gamma y • D)
    x (T*M) beta 0 1 (mul_nonneg hT0 hM) hb (by omega) hTerm0
  have hTerm1 : HasCoordinateWordJetBound N (fun y => Ea y • Kc b y) x (T*M^2) beta 0 := by
    have ht := hasCoordinateWordJetBound_smul N Ea (Kc b) (hES a) (hKS b) x M M beta 0 0 hM hM hb0 (hE a j) (hK b)
    convert ht using 1 <;> dsimp [T] <;> ring
  have hTerm1' := hasCoordinateWordJetBound_raise_degree N (fun y => Ea y • Kc b y)
    x (T*M^2) beta 0 1 (mul_nonneg hT0 (sq_nonneg M)) hb (by omega) hTerm1
  have hTerm2 : HasCoordinateWordJetBound N (fun y => Eb y • Kc a y) x (T*M^2) beta 0 := by
    have ht := hasCoordinateWordJetBound_smul N Eb (Kc a) (hES b) (hKS a) x M M beta 0 0 hM hM hb0 (hE b j) (hK a)
    convert ht using 1 <;> dsimp [T] <;> ring
  have hTerm2' := hasCoordinateWordJetBound_raise_degree N (fun y => Eb y • Kc a y)
    x (T*M^2) beta 0 1 (mul_nonneg hT0 (sq_nonneg M)) hb (by omega) hTerm2
  have hScalar1 : HasCoordinateWordJetBound N (fun y => fc b y*Ea y) x (T*F*M) beta 1 :=
    hasCoordinateWordJetBound_mul N (fc b) Ea (hfS b) (hES a) x F M beta 1 0 hF hM hb0 (hf b) (hE a j)
  have hScalar2 : HasCoordinateWordJetBound N (fun y => fc a y*Eb y) x (T*F*M) beta 1 :=
    hasCoordinateWordJetBound_mul N (fc a) Eb (hfS a) (hES b) x F M beta 1 0 hF hM hb0 (hf a) (hE b j)
  have hScalar : HasCoordinateWordJetBound N (fun y => fc b y*Ea y+fc a y*Eb y)
      x (2*T*F*M) beta 1 := by
    have ht := hasCoordinateWordJetBound_add N _ _ ((hfS b).mul (hES a)) ((hfS a).mul (hES b))
      x (T*F*M) (T*F*M) beta 1 hScalar1 hScalar2
    have he : T*F*M+T*F*M=2*T*F*M := by ring
    rwa [he] at ht
  have hTerm3 : HasCoordinateWordJetBound N
      (fun y => (fc b y*Ea y+fc a y*Eb y) • IminusD) x (4*T^2*F*M) beta 1 := by
    have ht := hasCoordinateWordJetBound_smul N _ (fun _ : R3 => IminusD)
      (((hfS b).mul (hES a)).add ((hfS a).mul (hES b))) contDiff_const
      x (2*T*F*M) 2 beta 1 0 (by positivity) (by norm_num) hb0 hScalar hIDjet
    have he : (2:ℝ)^N*(2*T*F*M)*2=4*T^2*F*M := by dsimp [T]; ring
    rwa [he] at ht
  have hSum01 := hasCoordinateWordJetBound_add N _ _ (hGammaS.neg.smul contDiff_const)
    ((hES a).smul (hKS b)) x (T*M) (T*M^2) beta 1 hTerm0' hTerm1'
  have hSum012 := hasCoordinateWordJetBound_add N _ _
    ((hGammaS.neg.smul contDiff_const).add ((hES a).smul (hKS b)))
    ((hES b).smul (hKS a)) x (T*M+T*M^2) (T*M^2) beta 1 hSum01 hTerm2'
  have hSum := hasCoordinateWordJetBound_add N _ _
    (((hGammaS.neg.smul contDiff_const).add ((hES a).smul (hKS b))).add ((hES b).smul (hKS a)))
    ((((hfS b).mul (hES a)).add ((hfS a).mul (hES b))).smul contDiff_const)
    x (T*M+T*M^2+T*M^2) (4*T^2*F*M) beta 1 hSum012 hTerm3
  have he : T*M+T*M^2+T*M^2+4*T^2*F*M=firstBaseJetConstant N M F := by unfold firstBaseJetConstant; dsimp [T]; ring
  rw [he] at hSum
  exact hSum

lemma hasCoordinateWordJetBound_referenceCovectorZeroBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (N : ℕ) (x : R3) (M F beta : ℝ)
    (hM : 0 ≤ M) (hF : 0 ≤ F) (hb : 1 ≤ beta)
    (hK : ∀ a, HasCoordinateWordJetBound N
      (fun y => normalizedReferenceAngularConnection hO hD g L lam y
        (referenceMetricGramFrame g L (lam,y) a)) x M beta 0)
    (hdK : ∀ a b, HasCoordinateWordJetBound N
      (fun y => directionalFDeriv (referenceMetricGramFrame g L (lam,y) a)
        (fun v => normalizedReferenceAngularConnection hO hD g L lam v
          (referenceMetricGramFrame g L (lam,v) b)) y) x M beta 0)
    (hkappa : ∀ a c b, HasCoordinateWordJetBound N
      (fun y => referenceFrameConnectionCoefficient g L lam y
        (referenceMetricGramFrame g L (lam,y) a) c b) x M beta 0)
    (hf : ∀ a, HasCoordinateWordJetBound N
      (referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)))
      x F beta 1)
    (hdf : ∀ a b, HasCoordinateWordJetBound N
      (fun y => directionalFDeriv (referenceMetricGramFrame g L (lam,y) a)
        (referenceFrameDerivative g L lam b (fun v => Real.log (referenceRadius δ R p L v))) y)
      x F beta 2)
    (a b : Fin 3) :
    HasCoordinateWordJetBound N
      (referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a b)
      x (secondBaseJetConstant N M F) beta 2 := by
  have hb0 : 0 ≤ beta := by linarith
  let T : ℝ := (2:ℝ)^N
  let Z : ℝ := zeroBaseJetConstant N M F
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hZ0 : 0 ≤ Z := zeroBaseJetConstant_nonneg N M F hM hF
  let Kc : Fin 3 → R3 → SphereL2 →L[ℝ] SphereL2 := fun c y =>
    normalizedReferenceAngularConnection hO hD g L lam y (referenceMetricGramFrame g L (lam,y) c)
  let fc : Fin 3 → R3 → ℝ := fun c => referenceFrameDerivative g L lam c
    (fun y => Real.log (referenceRadius δ R p L y))
  let Zc : Fin 3 → R3 → SphereL2 →L[ℝ] SphereL2 := fun c =>
    referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p c
  let kappa : Fin 3 → R3 → ℝ := fun c y => referenceFrameConnectionCoefficient g L lam y
    (referenceMetricGramFrame g L (lam,y) a) c b
  let dK : R3 → SphereL2 →L[ℝ] SphereL2 := fun y =>
    directionalFDeriv (referenceMetricGramFrame g L (lam,y) a) (Kc b) y
  let df : R3 → ℝ := fun y => directionalFDeriv (referenceMetricGramFrame g L (lam,y) a) (fc b) y
  let D : SphereL2 →L[ℝ] SphereL2 := inverseDegreeMultiplier hO hD
  let DminusSquare : SphereL2 →L[ℝ] SphereL2 := D-D.comp D
  have hKS (c : Fin 3) : ContDiff ℝ ∞ (Kc c) := contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam c
  have hfS (c : Fin 3) : ContDiff ℝ ∞ (fc c) := contDiff_referenceFrameDerivative g hg L lam c _
    (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have hZS (c : Fin 3) : ContDiff ℝ ∞ (Zc c) :=
    contDiff_referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p hδ hR c
  have hdKS : ContDiff ℝ ∞ dK := ((hKS b).fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiff_referenceMetricGramFrame_slice g hg L lam a)
  have hdfS : ContDiff ℝ ∞ df := ((hfS b).fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiff_referenceMetricGramFrame_slice g hg L lam a)
  have hkappaS (c : Fin 3) : ContDiff ℝ ∞ (kappa c) := by
    have he : (fun y => referenceFrameConnectionJoint g L
        (fun z : ℝ × R3 => referenceMetricGramFrame g L z a) (lam,y) c b) = kappa c := by
      funext y
      exact referenceFrameConnectionJoint_eq g hg L
        (fun z : ℝ × R3 => referenceMetricGramFrame g L z a) (lam,y) c b
    rw [← he]
    exact (contDiff_referenceFrameConnectionJoint g hg L
      (fun z : ℝ × R3 => referenceMetricGramFrame g L z a)
      (contDiff_referenceMetricGramFrame g hg L a) c b).comp (contDiff_const.prodMk contDiff_id)
  have hDjet : HasCoordinateWordJetBound N (fun _ : R3 => D) x 1 beta 0 :=
    hasCoordinateWordJetBound_const_normed N D x 1 beta (norm_inverseDegreeMultiplier_le_one hO hD) hb0
  have hDSjet : HasCoordinateWordJetBound N (fun _ : R3 => DminusSquare) x 2 beta 0 :=
    hasCoordinateWordJetBound_const_normed N DminusSquare x 2 beta
      (norm_inverseDegreeMultiplier_sub_square_le_two hO hD) hb0
  have hZjet (c : Fin 3) : HasCoordinateWordJetBound N (Zc c) x Z beta 1 :=
    hasCoordinateWordJetBound_referenceWeightedZeroBaseNormalizedCoefficient
      hO hD g hg L lam δ R p hδ hR N x M F beta hM hF hb hK hf c
  have hZD (c : Fin 3) : HasCoordinateWordJetBound N (fun y => (Zc c y).comp D) x (T*Z) beta 1 := by
    have ht := hasCoordinateWordJetBound_clm_comp N (Zc c) (fun _ : R3 => D)
      (hZS c) contDiff_const x Z 1 beta 1 0 hZ0 (by norm_num) hb0 (hZjet c) hDjet
    simpa only [T,mul_one,Nat.add_zero] using ht
  have hTerm0 : HasCoordinateWordJetBound N (fun y => (dK y).comp D) x (T*M) beta 0 := by
    have ht := hasCoordinateWordJetBound_clm_comp N dK (fun _ : R3 => D)
      hdKS contDiff_const x M 1 beta 0 0 hM (by norm_num) hb0 (hdK a b) hDjet
    simpa only [T,mul_one,Nat.zero_add] using ht
  have hTerm0' := hasCoordinateWordJetBound_raise_degree N (fun y => (dK y).comp D)
    x (T*M) beta 0 2 (mul_nonneg hT0 hM) hb (by omega) hTerm0
  have hTerm1 : HasCoordinateWordJetBound N (fun y => df y • DminusSquare) x (2*T*F) beta 2 := by
    have ht := hasCoordinateWordJetBound_smul N df (fun _ : R3 => DminusSquare)
      hdfS contDiff_const x F 2 beta 2 0 hF (by norm_num) hb0 (hdf a b) hDSjet
    have he : (2:ℝ)^N*F*2=2*T*F := by dsimp [T]; ring
    rwa [he] at ht
  have hTerm2 : HasCoordinateWordJetBound N (fun y => (Kc a y).comp (Zc b y)) x (T*M*Z) beta 1 :=
    hasCoordinateWordJetBound_clm_comp N (Kc a) (Zc b) (hKS a) (hZS b)
      x M Z beta 0 1 hM hZ0 hb0 (hK a) (hZjet b)
  have hTerm2' := hasCoordinateWordJetBound_raise_degree N (fun y => (Kc a y).comp (Zc b y))
    x (T*M*Z) beta 1 2 (by positivity) hb (by omega) hTerm2
  have hIndex (c : Fin 3) : HasCoordinateWordJetBound N
      (fun y => kappa c y • (Zc c y).comp D) x (T^2*M*Z) beta 1 := by
    have ht := hasCoordinateWordJetBound_smul N (kappa c) (fun y => (Zc c y).comp D)
      (hkappaS c) ((hZS c).clm_comp contDiff_const)
      x M (T*Z) beta 0 1 hM (mul_nonneg hT0 hZ0) hb0 (hkappa a c b) (hZD c)
    have he : (2:ℝ)^N*M*(T*Z)=T^2*M*Z := by dsimp [T]; ring
    rwa [he] at ht
  have hIndexS (c : Fin 3) : ContDiff ℝ ∞ (fun y => kappa c y • (Zc c y).comp D) :=
    (hkappaS c).smul ((hZS c).clm_comp contDiff_const)
  have hTerm3 : HasCoordinateWordJetBound N
      (fun y => ∑ c : Fin 3, kappa c y • (Zc c y).comp D) x (3*T^2*M*Z) beta 1 := by
    have ht := hasCoordinateWordJetBound_sum N
      (fun c : Fin 3 => fun y => kappa c y • (Zc c y).comp D) hIndexS x (T^2*M*Z) beta 1 hIndex
    simpa only [Fintype.card_fin,Nat.cast_ofNat,mul_assoc] using ht
  have hTerm3' := hasCoordinateWordJetBound_raise_degree N
    (fun y => ∑ c : Fin 3, kappa c y • (Zc c y).comp D)
    x (3*T^2*M*Z) beta 1 2 (by positivity) hb (by omega) hTerm3
  have hDifference : HasCoordinateWordJetBound N
      (fun y => Zc b y-(Zc b y).comp D) x (Z+T*Z) beta 1 :=
    hasCoordinateWordJetBound_sub N (Zc b) (fun y => (Zc b y).comp D)
      (hZS b) ((hZS b).clm_comp contDiff_const) x Z (T*Z) beta 1 (hZjet b) (hZD b)
  have hTerm4 : HasCoordinateWordJetBound N
      (fun y => fc a y • (Zc b y-(Zc b y).comp D)) x (T*F*(Z+T*Z)) beta 2 :=
    hasCoordinateWordJetBound_smul N (fc a) (fun y => Zc b y-(Zc b y).comp D)
      (hfS a) ((hZS b).sub ((hZS b).clm_comp contDiff_const))
      x F (Z+T*Z) beta 1 1 hF (by positivity) hb0 (hf a) hDifference
  have hSum01 := hasCoordinateWordJetBound_add N _ _ (hdKS.clm_comp contDiff_const)
    (hdfS.smul contDiff_const) x (T*M) (2*T*F) beta 2 hTerm0' hTerm1
  have hSum012 := hasCoordinateWordJetBound_add N _ _
    ((hdKS.clm_comp contDiff_const).add (hdfS.smul contDiff_const)) ((hKS a).clm_comp (hZS b))
    x (T*M+2*T*F) (T*M*Z) beta 2 hSum01 hTerm2'
  have hIndexTotalS : ContDiff ℝ ∞
      (fun y : R3 => ∑ c : Fin 3, kappa c y • (Zc c y).comp D) :=
    ContDiff.sum (fun c _ => hIndexS c)
  have hSub := hasCoordinateWordJetBound_sub N _ _
    (((hdKS.clm_comp contDiff_const).add (hdfS.smul contDiff_const)).add ((hKS a).clm_comp (hZS b)))
    hIndexTotalS
    x (T*M+2*T*F+T*M*Z) (3*T^2*M*Z) beta 2 hSum012 hTerm3'
  have hSum := hasCoordinateWordJetBound_add N _ _
    ((((hdKS.clm_comp contDiff_const).add (hdfS.smul contDiff_const)).add ((hKS a).clm_comp (hZS b))).sub
      hIndexTotalS)
    ((hfS a).smul ((hZS b).sub ((hZS b).clm_comp contDiff_const)))
    x (T*M+2*T*F+T*M*Z+3*T^2*M*Z) (T*F*(Z+T*Z)) beta 2 hSub hTerm4
  have he : T*M+2*T*F+T*M*Z+3*T^2*M*Z+T*F*(Z+T*Z)=secondBaseJetConstant N M F := by
    unfold secondBaseJetConstant
    dsimp [T,Z]
  rw [he] at hSum
  exact hSum

theorem exists_referenceDD_normalized_pair_uniform_coordinate_word_bounds
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (fun y => Real.log (referenceRadius δ R p L y)) x
      1 ≤ beta →
      (∀ a, HasCoordinateWordJetBound N
        (referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a) x C beta 1) ∧
      (∀ a b j, HasCoordinateWordJetBound N
        (referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p a b j) x C beta 1) ∧
      (∀ a b, HasCoordinateWordJetBound N
        (referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a b) x C beta 2) := by
  obtain ⟨M,hM,hgeometry⟩ := exists_referenceDD_fixed_geometry_uniform_coordinate_word_bounds hO hD g hg L K hK N
  obtain ⟨F0,hF0,hlog⟩ := exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds g hg L hL K hK N
  let F : ℝ := 1+F0
  have hM0 : 0 ≤ M := by linarith
  have hF0' : 0 ≤ F := by dsimp [F]; linarith
  have hF0F : F0 ≤ F := by dsimp [F]; linarith
  have hZ0 := zeroBaseJetConstant_nonneg N M F hM0 hF0'
  have hB0 := firstBaseJetConstant_nonneg N M F hM0 hF0'
  have hC0 := secondBaseJetConstant_nonneg N M F hM0 hF0'
  let C : ℝ := 1+zeroBaseJetConstant N M F+firstBaseJetConstant N M F+secondBaseJetConstant N M F
  have hC : 0 < C := by dsimp [C]; linarith
  have hZC : zeroBaseJetConstant N M F ≤ C := by dsimp [C]; linarith
  have hBC : firstBaseJetConstant N M F ≤ C := by dsimp [C]; linarith
  have hCC : secondBaseJetConstant N M F ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx beta hb
  have hb0 : 0 ≤ beta := by linarith
  have hGeometry (w : List (Fin 3)) (hw : w.length ≤ N) := hgeometry lam hlam x hx w hw
  have hMweight (w : List (Fin 3)) : M ≤ M*beta^w.length := by
    have ht := mul_le_mul_of_nonneg_left (one_le_pow₀ hb : 1 ≤ beta^w.length) hM0
    simpa only [mul_one] using ht
  have hEntry (a j : Fin 3) : HasCoordinateWordJetBound N
      (fun y => referenceMetricGramFrame g L (lam,y) a j) x M beta 0 := by
    intro w hw
    obtain ⟨_,he,_,_,_,_,_⟩ := hGeometry w hw
    simpa only [Real.norm_eq_abs,Nat.zero_add] using (he a j).trans (hMweight w)
  have hGamma (a b j : Fin 3) : HasCoordinateWordJetBound N
      (fun y => referenceConnectionFamily g L (lam,y) (referenceMetricGramFrame g L (lam,y) a)
        (referenceMetricGramFrame g L (lam,y) b) j) x M beta 0 := by
    intro w hw
    obtain ⟨_,_,_,_,hGamma,_,_⟩ := hGeometry w hw
    simpa only [Real.norm_eq_abs,Nat.zero_add] using (hGamma a b j).trans (hMweight w)
  have hKjet (a : Fin 3) : HasCoordinateWordJetBound N
      (fun y => normalizedReferenceAngularConnection hO hD g L lam y
        (referenceMetricGramFrame g L (lam,y) a)) x M beta 0 := by
    intro w hw
    obtain ⟨_,_,_,_,_,hKjet,_⟩ := hGeometry w hw
    simpa only [Nat.zero_add] using (hKjet a).trans (hMweight w)
  have hdKjet (a b : Fin 3) : HasCoordinateWordJetBound N
      (fun y => directionalFDeriv (referenceMetricGramFrame g L (lam,y) a)
        (fun v => normalizedReferenceAngularConnection hO hD g L lam v
          (referenceMetricGramFrame g L (lam,v) b)) y) x M beta 0 := by
    intro w hw
    obtain ⟨_,_,_,_,_,_,hdKjet⟩ := hGeometry w hw
    simpa only [Nat.zero_add] using (hdKjet a b).trans (hMweight w)
  have hkappa (a c b : Fin 3) : HasCoordinateWordJetBound N
      (fun y => referenceFrameConnectionCoefficient g L lam y
        (referenceMetricGramFrame g L (lam,y) a) c b) x M beta 0 := by
    intro w hw
    obtain ⟨_,_,_,hkappa,_,_,_⟩ := hGeometry w hw
    simpa only [Real.norm_eq_abs,Nat.zero_add] using (hkappa a c b).trans (hMweight w)
  have hfjet (a : Fin 3) : HasCoordinateWordJetBound N
      (referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y))) x F beta 1 := by
    intro w hw
    have ht := (hlog lam hlam δ hδ hδ1 R hR p hp x hx hb w hw).1 a
    have ht' := ht.trans (mul_le_mul_of_nonneg_right hF0F (pow_nonneg hb0 _))
    simpa only [Real.norm_eq_abs] using ht'
  have hdfjet (a b : Fin 3) : HasCoordinateWordJetBound N
      (fun y => directionalFDeriv (referenceMetricGramFrame g L (lam,y) a)
        (referenceFrameDerivative g L lam b (fun v => Real.log (referenceRadius δ R p L v))) y) x F beta 2 := by
    intro w hw
    have ht := (hlog lam hlam δ hδ hδ1 R hR p hp x hx hb w hw).2 a b
    have ht' := ht.trans (mul_le_mul_of_nonneg_right hF0F (pow_nonneg hb0 _))
    simpa only [Real.norm_eq_abs] using ht'
  refine ⟨?_,?_,?_⟩
  · intro a
    exact hasCoordinateWordJetBound_mono N _ x (zeroBaseJetConstant N M F) C beta 1
      (hasCoordinateWordJetBound_referenceWeightedZeroBaseNormalizedCoefficient
        hO hD g hg L lam δ R p hδ hR N x M F beta hM0 hF0' hb hKjet hfjet a) hZC hb0
  · intro a b j
    exact hasCoordinateWordJetBound_mono N _ x (firstBaseJetConstant N M F) C beta 1
      (hasCoordinateWordJetBound_referenceCovectorFirstBaseNormalizedCoefficient
        hO hD g hg L lam δ R p hδ hR N x M F beta hM0 hF0' hb hEntry hGamma hKjet hfjet a b j) hBC hb0
  · intro a b
    exact hasCoordinateWordJetBound_mono N _ x (secondBaseJetConstant N M F) C beta 2
      (hasCoordinateWordJetBound_referenceCovectorZeroBaseNormalizedCoefficient
        hO hD g hg L lam δ R p hδ hR N x M F beta hM0 hF0' hb hKjet hdKjet hkappa hfjet hdfjet a b) hCC hb0

theorem exists_referenceDD_normalized_trace_uniform_coordinate_word_smallness
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (N : ℕ) (hN : N ≤ 8) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField, ContDiff ℝ ∞ h → ∀ x ∈ K,
      let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (fun y => Real.log (referenceRadius δ R p L y)) x
      1 ≤ beta → coordinateH8 h x ≤ eps*referenceRadius δ R p L x →
      referenceRadius δ R p L x*beta^2 ≤ eps → ∀ w : List (Fin 3), w.length ≤ N →
      (∀ j, ‖coordinateFieldWordPartial w
        (referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j) x‖ ≤
          (C*eps/beta)*beta^w.length) ∧
      ‖coordinateFieldWordPartial w
        (referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h) x‖ ≤
          C*eps*beta^w.length := by
  obtain ⟨A,hA,hpair⟩ := exists_referenceDD_normalized_pair_uniform_coordinate_word_bounds hO hD g hg L hL K hK N
  obtain ⟨Cr,hCr,hradius⟩ := exists_referenceRadius_uniform_coordinate_word_bounds g hg L hL K hK N
  obtain ⟨H,hH,hcoframe⟩ := exists_physicalMixedFrameCoefficient_uniform_coordinate_word_bounds g hg L K hK N hN
  let Q : ℝ := 1+H
  let T : ℝ := (2:ℝ)^N
  let C : ℝ := 9*T^2*Cr*Q*A
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hT : 0 < T := by dsimp [T]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh x hx beta hb hH8 hsmall w hw
  have hbpos : 0 < beta := by linarith
  have hb0 : 0 ≤ beta := hbpos.le
  let r0 : ℝ := referenceRadius δ R p L x
  have hr0 : 0 < r0 := referenceRadius_pos δ R p L x hδ hR
  have hhComponent (i j : Fin 3) : ContDiff ℝ ∞ (fun y => h y i j) :=
    (contDiff_apply_apply ℝ ℝ i j).comp hh
  have hQS (a b : Fin 3) : ContDiff ℝ ∞ (physicalMixedQFrameCoefficient g L lam h a b) :=
    contDiff_physicalMixedQFrameCoefficient g hg L lam h hhComponent a b
  have hQjet (a b : Fin 3) : HasCoordinateWordJetBound N
      (physicalMixedQFrameCoefficient g L lam h a b) x Q beta 0 := by
    intro v hv
    have ht := (hcoframe lam hlam δ R hδ hR p eps beta heps heps1 hb h hhComponent x hx hH8 hsmall a b v hv).2
    simpa only [Real.norm_eq_abs,Q,Nat.zero_add] using ht
  have hRjet : HasCoordinateWordJetBound N (referenceRadius δ R p L) x (Cr*r0) beta 0 := by
    intro v hv
    have ht := (hradius lam hlam δ hδ hδ1 R hR p hp x hx v hv).1
    simpa only [Real.norm_eq_abs,r0,Nat.zero_add,mul_assoc] using ht
  obtain ⟨_,hBjet,hCjet⟩ := hpair lam hlam δ hδ hδ1 R hR p hp x hx hb
  have hTrace (s : ℕ) (V : Fin 3 → Fin 3 → R3 → SphereL2 →L[ℝ] SphereL2)
      (hVS : ∀ a b, ContDiff ℝ ∞ (V a b))
      (hV : ∀ a b, HasCoordinateWordJetBound N (V a b) x A beta s) :
      HasCoordinateWordJetBound N
        (fun y => referenceRadius δ R p L y • ∑ a : Fin 3, ∑ b : Fin 3,
          physicalMixedQFrameCoefficient g L lam h a b y • V a b y) x (C*r0) beta s := by
    have hTermS (a b : Fin 3) : ContDiff ℝ ∞
        (fun y => physicalMixedQFrameCoefficient g L lam h a b y • V a b y) :=
      (hQS a b).smul (hVS a b)
    have hTerm (a b : Fin 3) : HasCoordinateWordJetBound N
        (fun y => physicalMixedQFrameCoefficient g L lam h a b y • V a b y) x (T*Q*A) beta s := by
      simpa only [T, Nat.zero_add] using
        hasCoordinateWordJetBound_smul N _ _ (hQS a b) (hVS a b)
          x Q A beta 0 s hQ.le hA.le hb0 (hQjet a b) (hV a b)
    have hSumS (a : Fin 3) : ContDiff ℝ ∞
        (fun y => ∑ b : Fin 3, physicalMixedQFrameCoefficient g L lam h a b y • V a b y) :=
      ContDiff.sum (fun b _ => hTermS a b)
    have hSum (a : Fin 3) : HasCoordinateWordJetBound N
        (fun y => ∑ b : Fin 3, physicalMixedQFrameCoefficient g L lam h a b y • V a b y)
        x (3*T*Q*A) beta s := by
      simpa only [Fintype.card_fin,Nat.cast_ofNat,mul_assoc] using hasCoordinateWordJetBound_sum N
        (fun b : Fin 3 => fun y => physicalMixedQFrameCoefficient g L lam h a b y • V a b y)
        (hTermS a) x (T*Q*A) beta s (hTerm a)
    have hTotalS : ContDiff ℝ ∞
        (fun y => ∑ a : Fin 3, ∑ b : Fin 3, physicalMixedQFrameCoefficient g L lam h a b y • V a b y) :=
      ContDiff.sum (fun a _ => hSumS a)
    have hTotal : HasCoordinateWordJetBound N
        (fun y => ∑ a : Fin 3, ∑ b : Fin 3, physicalMixedQFrameCoefficient g L lam h a b y • V a b y)
        x (9*T*Q*A) beta s := by
      have ht := hasCoordinateWordJetBound_sum N
        (fun a : Fin 3 => fun y => ∑ b : Fin 3, physicalMixedQFrameCoefficient g L lam h a b y • V a b y)
        hSumS x (3*T*Q*A) beta s hSum
      have he : (Fintype.card (Fin 3) : ℝ)*(3*T*Q*A)=9*T*Q*A := by norm_num; ring
      rwa [he] at ht
    have ht := hasCoordinateWordJetBound_smul N (referenceRadius δ R p L) _
      (contDiff_referenceRadius_actual δ R p L hδ hR) hTotalS
      x (Cr*r0) (9*T*Q*A) beta 0 s (mul_nonneg hCr.le hr0.le) (by positivity) hb0 hRjet hTotal
    have he : (2:ℝ)^N*(Cr*r0)*(9*T*Q*A)=C*r0 := by dsimp [C,T]; ring
    rw [he] at ht
    simpa only [Nat.zero_add] using ht
  have hFirst (j : Fin 3) : HasCoordinateWordJetBound N
      (referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j) x (C*r0) beta 1 := by
    have he : referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j =
        fun y => referenceRadius δ R p L y • ∑ a : Fin 3, ∑ b : Fin 3,
          physicalMixedQFrameCoefficient g L lam h a b y •
            referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p a b j y := by
      funext y
      exact referenceWeightedFirstBaseNormalizedCoefficient_eq_sum hO hD g hg L lam δ R p h j y
    rw [he]
    exact hTrace 1 (fun a b => referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p a b j)
      (fun a b => contDiff_referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p hδ hR a b j)
      (fun a b => hBjet a b j)
  have hZero : HasCoordinateWordJetBound N
      (referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h) x (C*r0) beta 2 :=
    hTrace 2 (fun a b => referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a b)
      (fun a b => contDiff_referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p hδ hR a b)
      hCjet
  have hsmall' : r0*beta^2 ≤ eps := hsmall
  have hFirstSmall : C*r0*beta ≤ C*eps/beta := by
    apply (le_div_iff₀ hbpos).mpr
    calc
      C*r0*beta*beta = C*(r0*beta^2) := by ring
      _ ≤ C*eps := mul_le_mul_of_nonneg_left hsmall' hC.le
  have hZeroSmall : C*(r0*beta^2) ≤ C*eps := mul_le_mul_of_nonneg_left hsmall' hC.le
  refine ⟨?_,?_⟩
  · intro j
    apply (hFirst j w hw).trans
    calc
      (C*r0)*beta^(1+w.length) = (C*r0*beta)*beta^w.length := by rw [pow_add,pow_one]; ring
      _ ≤ (C*eps/beta)*beta^w.length := mul_le_mul_of_nonneg_right hFirstSmall (pow_nonneg hb0 _)
  · apply (hZero w hw).trans
    calc
      (C*r0)*beta^(2+w.length) = (C*(r0*beta^2))*beta^w.length := by rw [pow_add]; ring
      _ ≤ C*eps*beta^w.length := mul_le_mul_of_nonneg_right hZeroSmall (pow_nonneg hb0 _)

end OAI.AnisotropicCalderon.ActualReferenceDDHigherActualCoefficients
