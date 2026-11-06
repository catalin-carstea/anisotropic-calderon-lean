import Calderon.ActualTSZeroFirstBilinearCaps
import Calderon.ActualTSZeroFirstPointwise

/-! Weighted Green integrals for every one of the 270 D01 symmetric triples.
The same room supplies all coefficient caps. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstSymmetricIntegral
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAllAngularAtomGainedRoom ActualHigherSFormation
  ActualRetainedGeneratorMultiplierGains ActualHigherSScalarCommutatorNativeForm
  ActualHigherSZeroScalarNativeForm
  ActualTSZeroFirstPointwise ActualTSZeroFirstEnergyTools ActualTSZeroFirstBilinearCaps
  ActualTSSymmetricFirstGreen ActualHigherSScalarCommutatorForm ActualHigherSZeroScalarCommutatorForm
  PrincipalCommutator ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highDualNormed : NormedAddCommGroup (Hi →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def highDualSpace : NormedSpace ℝ (Hi →L[ℝ] ℝ) := inferInstance
attribute [local instance] highDualNormed highDualSpace
@[instance_reducible] private def highBidualNormed : NormedAddCommGroup ((Hi →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def highBidualSpace : NormedSpace ℝ ((Hi →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
attribute [local instance] highBidualNormed highBidualSpace
@[instance_reducible] private def evaluationNormed : NormedAddCommGroup (Hi →L[ℝ] (Hi →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def evaluationSpace : NormedSpace ℝ (Hi →L[ℝ] (Hi →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
attribute [local instance] evaluationNormed evaluationSpace
attribute [local instance] ActualTSActualTripleRoomCaps.tripleCoefficientNormedGroup
  ActualTSActualTripleRoomCaps.tripleCoefficientNormedSpace
  ActualTSActualTripleRoomCaps.spatialTripleCoefficientNormedGroup
  ActualTSActualTripleRoomCaps.spatialTripleCoefficientNormedSpace
variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
  (ε C ρ : ℝ) (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
local notation "ARoom" d:max => AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d
local notation "UF" => higherSInput hO hD
local notation "SD" => zeroFirstSymmetricWordDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "WCoeff" => zeroFirstWeightedTripleCoefficient
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

private theorem symmetric_density_eq
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) (k j i : Fin 3) (V : Generator) :
    symmetricFirstDensity (evaluationPairing : Hi →L[ℝ] (Hi →L[ℝ] ℝ) →L[ℝ] ℝ)
      (fun x => referenceDensityFamily g L (q,x)) (UF F)
      (WCoeff g2 q dr Ar p k j i V) (coordinateDirection k) =
      (fun x => referenceDensityFamily g L (q,x)*SD g2 q dr Ar p F k j i V x) := by
  funext x
  simp only [symmetricFirstDensity,evaluationPairing_apply,zeroFirstWeightedTripleCoefficient_apply,
    zeroFirstSymmetricWordDensity,directionalFDeriv]
  ring

/-- Every original symmetric row is integrable and controlled by the same
original inclusion energy, with constants selected before all profiles. -/
theorem exists_original_zero_first_symmetric_integral_bound
    (hL : 0 < L) {d : ℝ} (hd : 0 < d) (P : ARoom d)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Csym etaSym : ℝ, 0 < Csym ∧ 0 < etaSym ∧ etaSym ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaSym →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      ∀ k j i : Fin 3, ∀ V : Generator,
      Integrable (fun x => referenceDensityFamily g L (q,x)*SD g2 q dr Ar p F k j i V x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*SD g2 q dr Ar p F k j i V x| ≤
        Csym*eta*(∫ x, referenceDensityFamily g L (q,x)*
          inclusionEnergyDensity IH (actualReferenceBeta g L q dr Ar p x) (UF F) x) := by
  obtain ⟨Q,hQ,etaSym,heSym,heSym1,hWeight⟩ := exists_actual_uniform_zero_first_weighted_triple_first_caps
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hd P g2 hg2
  obtain ⟨M,hM,hDensity⟩ := exists_density_coordinate_relative_bound
    g hg L (closedBall y0 ρ) (isCompact_closedBall _ _)
  let Peval : Hi →L[ℝ] (Hi →L[ℝ] ℝ) →L[ℝ] ℝ := evaluationPairing
  let Cbase : ℝ := ‖Peval‖*Q*(M+1)
  let Csym : ℝ := Cbase+1
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hCbase : 0 ≤ Cbase := by dsimp only [Cbase]; positivity
  have hCsym : 0 < Csym := by dsimp only [Csym]; positivity
  refine ⟨Csym,etaSym,hCsym,heSym,heSym1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hSupp hb hs k j i V
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let beta := actualReferenceBeta g L q dr Ar p
  let u := UF F
  let A := WCoeff g2 q dr Ar p k j i V
  have hmu : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hmu0 (x : R3) : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (q,x)).le
  have hbeta : Continuous beta := continuous_actualReferenceBeta g hg L q dr Ar p hL hdr hAr
  have hbpos (x : R3) : 0 < beta x := actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp x
  have hu : ContDiff ℝ ∞ u := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hu0 (x : R3) (hx : x ∉ K) : u x=0 :=
    highInput_eq_zero_off hO hD F x (fun hy => hx (hSupp hy))
  have hW (x : R3) (hx : x ∈ K) := hWeight q hq dr hdr hdr1 Ar hAr p hp eta heta he x
    (ball_subset_closedBall (hKball hx)) (hKball hx) (hb x hx) (hs x hx) k j i V
  have hLift : ∀ x ∈ K, Q*eta ≤ Q*eta*beta x := fun x hx => by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb x hx) (mul_nonneg hQ.le heta)
  have hGreen := symmetric_first_integral_mass_bound Peval mu beta u A K hK hmu hbeta hbpos hu hu0
    (fun x hx => (hW x hx).1) (coordinateDirection k) Q M eta hQ.le hM0 heta hmu0
    (fun x hx => (hW x hx).2.1.trans (hLift x hx))
    (fun x hx => ((hW x hx).2.2 k).trans (hLift x hx))
    (fun x hx => hDensity q hq x (ball_subset_closedBall (hKball hx)) k)
  have hE : Integrable (fun x => mu x*inclusionEnergyDensity IH (beta x) u x) :=
    inclusionEnergy_integrable IH mu beta u K hK hmu.continuous hbeta (fun x => (hbpos x).ne') hu hu0
  have hMassCompact : HasCompactSupport (fun x => mu x*beta x*‖u x‖^2) := by
    apply HasCompactSupport.intro hK
    intro x hx
    change mu x*beta x*‖u x‖^2=0
    rw [hu0 x hx]
    simp only [norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero]
  have hMass : Integrable (fun x => mu x*beta x*‖u x‖^2) :=
    ((hmu.continuous.mul hbeta).mul (hu.continuous.norm.pow 2)).integrable_of_hasCompactSupport hMassCompact
  have hMassLe : (∫ x, mu x*beta x*‖u x‖^2) ≤
      ∫ x, mu x*inclusionEnergyDensity IH (beta x) u x := by
    apply integral_mono hMass hE
    intro x
    exact (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (inclusion_mass_le IH (beta x) u x (hbpos x).le) (hmu0 x))
  have hE0 : 0 ≤ ∫ x, mu x*inclusionEnergyDensity IH (beta x) u x :=
    integral_nonneg (fun x => mul_nonneg (hmu0 x) (inclusionEnergyDensity_nonneg IH (beta x) u x (hbpos x).le))
  have hId := symmetric_density_eq hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    g2 q dr Ar p F k j i V
  refine ⟨hId ▸ hGreen.1,?_⟩
  have hIntegralEq := congrArg (fun f : R3 → ℝ => ∫ x, f x) hId
  have hAbsEq := congrArg (fun z : ℝ => |z|) hIntegralEq
  have hG : |∫ x, mu x*SD g2 q dr Ar p F k j i V x| ≤
      Cbase*eta*(∫ x, mu x*beta x*‖u x‖^2) :=
    hAbsEq.symm.trans_le hGreen.2
  exact hG.trans ((mul_le_mul_of_nonneg_left hMassLe (mul_nonneg hCbase heta)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by dsimp only [Csym]; linarith : Cbase ≤ Csym) heta) hE0))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstSymmetricIntegral
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstSymmetricIntegral.exists_original_zero_first_symmetric_integral_bound
