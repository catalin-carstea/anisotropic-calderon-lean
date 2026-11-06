import Calderon.ActualHigherSScalarCommutatorForm
import Calderon.ActualOriginalSPhysicalReferenceForm
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSScalarCommutatorNativeForm
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
  PrincipalCommutator ActualScalarPrincipalAdjoint PerturbedDensityAdjoint ActualHigherSFirstCoefficientJets
  ActualHigherSScalarCommutatorCoefficients ActualHigherSScalarCommutatorForm ActualScalarPrincipalSelfFormBound
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

@[instance_reducible] private def negDualNormed : NormedAddCommGroup (Neg →L[ℝ] ℝ) := inferInstance
attribute [local instance] negDualNormed
@[instance_reducible] private def negDualSpace : NormedSpace ℝ (Neg →L[ℝ] ℝ) := inferInstance
attribute [local instance] negDualSpace
@[instance_reducible] private def coefficientLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] coefficientLowNormed
@[instance_reducible] private def coefficientLowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] coefficientLowSpace

/-- The actual half/negative Sobolev dual pairing as a continuous bilinear map. -/
def halfDualPairingL : Half →L[ℝ] Neg →L[ℝ] ℝ := innerSL ℝ (E := Half)
lemma halfDualPairingL_apply (v : Half) (z : Neg) :
    halfDualPairingL v z = sphereSobolevDualPairing (1/2 : ℝ) v z := rfl

private def pairingNorm : ℝ := ‖halfDualPairingL‖
private lemma pairingNorm_nonneg : 0 ≤ pairingNorm := norm_nonneg halfDualPairingL

/-- Normalize the actual density derivative before applying the fixed compact family bound. -/
theorem exists_density_coordinate_relative_bound (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ i : Fin 3,
      |directionalFDeriv (coordinateDirection i) (fun y => referenceDensityFamily g L (q,y)) x| ≤
        M*referenceDensityFamily g L (q,x) := by
  let f : Fin 3 → (ℝ × R3) → ℝ := fun i t =>
    (referenceDensityFamily g L t)⁻¹*familyDirectionalDeriv i (referenceDensityFamily g L) t
  have hf (i : Fin 3) : Continuous (f i) :=
    ((contDiff_referenceDensityFamily_inv g hg L).mul
      (contDiff_familyDirectionalDeriv i _ (contDiff_referenceDensityFamily g hg L))).continuous
  obtain ⟨M,hM,hcap⟩ := exists_uniform_bound_finite_family f hf K hK
  refine ⟨M,hM,?_⟩
  intro q hq x hx i
  have hm := referenceDensityFamily_pos g hg L (q,x)
  have he : referenceDensityFamily g L (q,x)*f i (q,x) =
      directionalFDeriv (coordinateDirection i) (fun y => referenceDensityFamily g L (q,y)) x := by
    dsimp [f,familyDirectionalDeriv]
    rw [←mul_assoc,mul_inv_cancel₀ hm.ne',one_mul]
  calc _ = |referenceDensityFamily g L (q,x)*f i (q,x)| := congrArg abs he.symm
       _ = referenceDensityFamily g L (q,x)*|f i (q,x)| := by rw [abs_mul,abs_of_pos hm]
       _ ≤ referenceDensityFamily g L (q,x)*M := mul_le_mul_of_nonneg_left (hcap q hq x hx i) hm.le
       _ = _ := mul_comm _ _

private lemma norm_clm_sq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (I : E →L[ℝ] F) (v : E) :
    ‖I v‖^2 ≤ ‖I‖^2*‖v‖^2 := by
  have h := mul_self_le_mul_self (norm_nonneg (I v)) (I.le_opNorm v)
  calc _ ≤ (‖I‖*‖v‖)^2 := by simpa only [pow_two] using h
       _ = _ := mul_pow _ _ _

section InputEnergy
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
/-- Genuine inclusion of the high finite input; the inclusion is not replaced by an identity. -/
def halfInput (F : smoothCompactFiniteSphereCore hO hD) : R3 → Half :=
  fun x => IH (ActualHigherSFormation.higherSInput hO hD F x)

lemma contDiff_halfInput (F : smoothCompactFiniteSphereCore hO hD) :
    ContDiff ℝ ∞ (halfInput hO hD F) :=
  (contDiff_const.clm_apply (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F))

lemma halfInput_eq_zero_off (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (hx : x ∉ tsupport F.val) : halfInput hO hD F x = 0 := by
  have hr := finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F
  have hxU : x ∉ tsupport (ActualHigherSFormation.higherSInput hO hD F) := fun h => hx (hr.2.2.1 h)
  simp only [halfInput,image_eq_zero_of_notMem_tsupport hxU,map_zero]

lemma directional_halfInput (F : smoothCompactFiniteSphereCore hO hD) (X x : R3) :
    directionalFDeriv X (halfInput hO hD F) x =
      IH (directionalFDeriv X (ActualHigherSFormation.higherSInput hO hD F) x) := by
  change directionalFDeriv X (fun y => IH (ActualHigherSFormation.higherSInput hO hD F y)) x = _
  have h := directionalFDeriv_clm_apply X (fun _ : R3 => IH)
    (ActualHigherSFormation.higherSInput hO hD F) contDiff_const
    (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F) x
  simpa only [halfInput,directionalFDeriv,fderiv_const_apply,zero_apply,map_zero,zero_add] using h

private lemma included_energy_scale (a b u d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : 0 ≤ u) (hd : 0 ≤ d) (w : ℝ) (hw : w ≤ a*u) :
    b⁻¹*d+b*w ≤ (a+1)*(b⁻¹*d+b*u) := by
  have h1 := mul_le_mul_of_nonneg_left hw hb
  have h2 : 0 ≤ a*b⁻¹*d+b*u := by positivity
  nlinarith only [h1,h2]

/-- Coordinate half-energy is controlled by the original reference energy, uniformly in finite angular size. -/
theorem exists_halfInput_coordinate_reference_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ Cr : ℝ, 0 < Cr ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ beta : ℝ, 1 ≤ beta →
      ∀ F : smoothCompactFiniteSphereCore hO hD,
        coordinateEnergyDensity coordinateDirection beta (halfInput hO hD F) x ≤
          Cr*finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x := by
  obtain ⟨Cr,hCr,hcap⟩ := exists_finiteCoreSourceEnergy_uniform_reference_profile_bound hO hD g hg L K hK
  refine ⟨(‖IH‖^2+1)*Cr,mul_pos (by positivity) hCr,?_⟩
  intro q hq x hx beta hb F
  let U := ActualHigherSFormation.higherSInput hO hD F
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hU : ‖halfInput hO hD F x‖^2 ≤ ‖IH‖^2*‖U x‖^2 := by
    change ‖IH (U x)‖^2 ≤ ‖IH‖^2*‖U x‖^2
    exact norm_clm_sq IH (U x)
  have hSum : (∑ i : Fin 3, ‖directionalFDeriv (coordinateDirection i) (halfInput hO hD F) x‖^2) =
      ∑ i : Fin 3, ‖IH (fderiv ℝ U x (coordinateDirection i))‖^2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [directional_halfInput hO hD F (coordinateDirection i) x]
    rfl
  have hScale := included_energy_scale (‖IH‖^2) beta (‖U x‖^2)
    (∑ i : Fin 3, ‖IH (fderiv ℝ U x (coordinateDirection i))‖^2)
    (sq_nonneg _) hb0 (sq_nonneg _) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    (‖halfInput hO hD F x‖^2) hU
  have hSource := native_threeHalf_angular_energy_le_finiteCoreSourceEnergy hO hD beta F x
  calc
    _ = beta⁻¹*(∑ i : Fin 3, ‖IH (fderiv ℝ U x (coordinateDirection i))‖^2)+
        beta*‖halfInput hO hD F x‖^2 := by rw [coordinateEnergyDensity,hSum]
    _ ≤ (‖IH‖^2+1)*(beta⁻¹*(∑ i : Fin 3, ‖IH (fderiv ℝ U x (coordinateDirection i))‖^2)+beta*‖U x‖^2) := hScale
    _ ≤ (‖IH‖^2+1)*finiteCoreSourceEnergy hO hD beta F x :=
      mul_le_mul_of_nonneg_left hSource (by positivity)
    _ ≤ (‖IH‖^2+1)*(Cr*finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x) :=
      mul_le_mul_of_nonneg_left (hcap q hq x hx beta hb F) (by positivity)
    _ = _ := by ring

/-- Native integrated coordinate/reference comparison, with every profile and angular input after Cr. -/
theorem exists_halfInput_coordinate_reference_integral_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ Cr : ℝ, 0 < Cr ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ δr Ar : ℝ, ∀ p : ℕ,
      0 < δr → 0 < Ar → 1 ≤ p → ∀ F : smoothCompactFiniteSphereCore hO hD,
      (tsupport F.val ⊆ K) →
      (∀ x ∈ tsupport F.val, 1 ≤ actualReferenceBeta g L q δr Ar p x) →
      coordinateEnergy coordinateDirection (fun x => referenceDensityFamily g L (q,x))
        (actualReferenceBeta g L q δr Ar p) (halfInput hO hD F) ≤
        Cr*∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q δr Ar p x) F x := by
  obtain ⟨Cr,hCr,hcap⟩ := exists_halfInput_coordinate_reference_bound hO hD g hg L K hK
  refine ⟨Cr,hCr,?_⟩
  intro q hq δr Ar p hδr hAr hp F hsub hbeta
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let beta := actualReferenceBeta g L q δr Ar p
  let u := halfInput hO hD F
  have hmu : ∀ x, 0 ≤ mu x := fun x => (referenceDensityFamily_pos g hg L (q,x)).le
  have hm : Continuous mu := (contDiff_referenceDensityFamily g hg L).continuous.comp
    (continuous_const.prodMk continuous_id)
  have hb := continuous_actualReferenceBeta g hg L q δr Ar p hL hδr hAr
  have hbpos := actualReferenceBeta_pos g hg L q δr Ar p hL hδr hAr hp
  have hu := contDiff_halfInput hO hD F
  have h0 : ∀ x ∉ tsupport F.val, u x = 0 := halfInput_eq_zero_off hO hD F
  have huc : HasCompactSupport u := HasCompactSupport.intro F.property.2.1 h0
  have hEi := coordinateEnergy_integrable coordinateDirection mu beta u hm hb hbpos hu huc
  have hNi := ActualFiniteHarmonicModel.integrable_finiteCoreReferenceProfileEnergy hO hD
    g hg L q beta hb hbpos F
  have hPt : ∀ x, mu x*coordinateEnergyDensity coordinateDirection (beta x) u x ≤
      Cr*(mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F x) := by
    intro x
    by_cases hx : x ∈ tsupport F.val
    · have h := mul_le_mul_of_nonneg_left (hcap q hq x (hsub hx) (beta x) (hbeta x hx) F) (hmu x)
      exact h.trans_eq (by ring)
    · have hu0 := h0 x hx
      have hd0 (i : Fin 3) := directional_eq_zero_off u (tsupport F.val)
        (isClosed_tsupport F.val) h0 (coordinateDirection i) x hx
      have hz : coordinateEnergyDensity coordinateDirection (beta x) u x = 0 := by
        simp only [coordinateEnergyDensity,hu0,hd0,norm_zero,zero_pow (by decide : 2 ≠ 0),
          Finset.sum_const_zero,mul_zero,add_zero]
      rw [hz,mul_zero]
      exact mul_nonneg hCr.le (mul_nonneg (hmu x)
        (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q (beta x) (hbpos x).le F x))
  have h := integral_mono hEi (hNi.const_mul Cr) hPt
  rw [integral_const_mul] at h
  exact h
end InputEnergy

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BCC" => canonicalFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "BETA" => actualReferenceBeta g L
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)

/-- The actual canonical first-coordinate S / actual scalar-principal composed negative commutator. -/
def nativeScalarFirstCommutator (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (h : MatrixField) (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) : Neg :=
  scalarFirstCoordinateCommutatorSum
    (fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j)
    (fun l y => BCC g2 δr Ar p q y l) (halfInput hO hD F0) x
local notation "NC" => nativeScalarFirstCommutator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Exact native form task with original perturbation and profile hypotheses, before all angular inputs. -/
def ActualScalarFirstFormBound (δ : ℝ) (g2 : MatrixField) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ,
    0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p → ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
    (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
    ∀ F0 : smoothCompactFiniteSphereCore hO hD,
      (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
      (∀ x ∈ TS F0, ∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps*referenceRadius δr Ar p L x)) →
      (∀ x ∈ TS F0, 1 ≤ BETA q δr Ar p x) →
      (∀ x ∈ TS F0, referenceRadius δr Ar p L x*(BETA q δr Ar p x)^2 ≤ eps) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        sphereSobolevDualPairing (1/2 : ℝ) (halfInput hO hD F0 x) (NC g2 δr Ar p q h F0 x)) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F0 x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*
        sphereSobolevDualPairing (1/2 : ℝ) (halfInput hO hD F0 x) (NC g2 δr Ar p q h F0 x)| ≤
        K*eps*∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F0 x
local notation "NativeForm" => ActualScalarFirstFormBound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Fixed native room: K after g2 and before every profile, perturbation and finite input. -/
theorem exists_actual_scalar_first_commutator_reference_form
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (hL : 0 < L)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) : NativeForm δ g2 := by
  obtain ⟨M,hM,hmuCap⟩ := exists_density_coordinate_relative_bound g hg L
    (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  obtain ⟨Cr,hCr,hEcap⟩ := exists_halfInput_coordinate_reference_integral_bound hO hD g hg L hL
    (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  obtain ⟨Q,hQ,hcap⟩ := exists_actual_scalar_first_coordinate_commutator_coefficient_bounds
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hL g2 hg2
  have hP : 0 ≤ pairingNorm := pairingNorm_nonneg
  have hM3 : 0 < M+3 := by linarith
  refine ⟨108*(pairingNorm+1)*Q*(M+3)*Cr,by positivity,?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq eps heps heps1 h hh F0 hTF hjet hbeta hsmall
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let beta := BETA q δr Ar p
  let u := halfInput hO hD F0
  let aa : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j
  let bb : Fin 3 → R3 → (Half →L[ℝ] Neg) := fun l y => BCC g2 δr Ar p q y l
  have hbcont := continuous_actualReferenceBeta g hg L q δr Ar p hL hδr hAr
  have hbpos := actualReferenceBeta_pos g hg L q δr Ar p hL hδr hAr hp
  have hK : IsCompact (TS F0) := F0.property.2.1
  have hu := contDiff_halfInput hO hD F0
  have hu0 : ∀ x ∉ TS F0, u x = 0 := halfInput_eq_zero_off hO hD F0
  have hsub : TS F0 ⊆ closedBall y0 ρ := by
    intro x hx
    simpa only [ActualHigherSFormation.higherSParam] using (hTF x hx).1.2.1
  have hm : ContDiff ℝ ∞ mu := (contDiff_referenceDensityFamily g hg L).comp
    (contDiff_const.prodMk contDiff_id)
  have hmu : ∀ x, 0 ≤ mu x := fun x => (referenceDensityFamily_pos g hg L (q,x)).le
  have ha : ∀ i j, ContDiff ℝ ∞ (aa i j) :=
    ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L q δr Ar p h hδr hAr hh
  have hb : ∀ l, ∀ x ∈ TS F0, ContDiffAt ℝ ∞ (bb l) x := by
    intro l x hx
    exact contDiffAt_canonicalFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q x (hTF x hx) l
  have hCaps : ∀ x ∈ TS F0, CoordinateCommutatorCoefficientBudget aa bb x eps 1 (beta x) Q := by
    intro x hx
    have hc := hcap δr Ar p hδr hδr1 hAr hp q hq eps heps heps1 h hh x
      (hTF x hx) (hjet x hx) (hbeta x hx) (hsmall x hx)
    have hr : 0 ≤ referenceRadius δr Ar p L x := (referenceRadius_pos δr Ar p L x hδr hAr).le
    have hb1 := hbeta x hx
    have hb2 : 1 ≤ (beta x)^2 := by nlinarith only [hb1]
    have hr1 : referenceRadius δr Ar p L x ≤ 1 := by
      have hs := (hsmall x hx).trans heps1
      have hn := mul_nonneg hr (sub_nonneg.mpr hb2)
      nlinarith only [hs,hn]
    exact coordinateCommutatorCoefficientBudget_radius_le_one aa bb x eps _ (beta x) Q
      heps hQ.le hr hr1 (hbpos x).le hc
  have hB := scalar_first_coordinate_commutator_sum_form_bound halfDualPairingL mu beta u aa bb
    (TS F0) hK hm hbcont hbpos hu hu0 ha hb Q M eps hQ.le (zero_le_one.trans hM) heps
    hmu hbeta (fun k x hx => hmuCap q hq x (hsub hx) k) hCaps
  have hN := integrable_finiteCoreReferenceProfileEnergy hO hD g hg L q beta hbcont hbpos F0
  have hE := hEcap q hq δr Ar p hδr hAr hp F0 hsub hbeta
  have hNI : 0 ≤ ∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F0 x :=
    integral_nonneg (fun x => mul_nonneg (hmu x)
      (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q (beta x) (hbpos x).le F0 x))
  have hEq : (fun x => mu x*sphereSobolevDualPairing (1/2 : ℝ) (u x) (NC g2 δr Ar p q h F0 x)) =
      (fun x => mu x*halfDualPairingL (u x) (scalarFirstCoordinateCommutatorSum aa bb u x)) := by
    funext x
    rw [halfDualPairingL_apply]
    rfl
  have hOrigI : Integrable (fun x => mu x*sphereSobolevDualPairing (1/2 : ℝ)
      (u x) (NC g2 δr Ar p q h F0 x)) := hEq.symm ▸ hB.1
  refine ⟨hOrigI,hN,?_⟩
  have hIEq := congrArg (fun J : R3 → ℝ => ∫ x, J x) hEq
  calc
    _ = |∫ x, mu x*halfDualPairingL (u x) (scalarFirstCoordinateCommutatorSum aa bb u x)| := congrArg abs hIEq
    _ ≤ (108*pairingNorm*Q*(M+3)*eps)*coordinateEnergy coordinateDirection mu beta u := hB.2
    _ ≤ (108*pairingNorm*Q*(M+3)*eps)*
        (Cr*∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F0 x) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ (108*(pairingNorm+1)*Q*(M+3)*Cr)*eps*
        (∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F0 x) := by
      have hpos : 0 ≤ 108*Q*(M+3)*Cr*eps*
          (∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F0 x) := by positivity
      nlinarith only [hpos]

/-- Same W and common room before g2, with actual native Jacobian guard retained. -/
theorem exists_retained_actual_scalar_first_commutator_reference_form
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ _Cm : CRoom hreg δ0 W δ,
      (∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z) ∧
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 → NativeForm δ g2 := by
  obtain ⟨δ,Cm,hJac⟩ := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  refine ⟨δ,Cm.rev.pos,Cm.rev.le0,Cm.rev.leρ,Cm,hJac,?_⟩
  intro g2 hg2
  exact exists_actual_scalar_first_commutator_reference_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hL g2 hg2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSScalarCommutatorNativeForm
