import Calderon.ActualMixedAngularWeightedSecondCaps
import Calderon.ActualHigherSScalarCommutatorNativeForm
import Calderon.ActualHigherSIntegratedPairing

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualMixedAngularPairedGains
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly PrincipalCommutator ReferenceDensityBounds
  ActualScalarPrincipalAdjoint ActualHigherSScalarCommutatorForm ActualScalarPrincipalSelfFormBound
  ActualHigherSScalarCommutatorNativeForm ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ConformalDepth ReferenceWeightedApproximation
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def mixedNegDualNormed : NormedAddCommGroup (Neg →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def mixedNegDualSpace : NormedSpace ℝ (Neg →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def mixedLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def mixedLowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] mixedNegDualNormed mixedNegDualSpace mixedLowNormed mixedLowSpace

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
local notation "CoeffRoom" => ActualFullEGainedEndpoints.CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q

/-- Canonical coordinate conversion in the small concrete operator space. -/
private theorem mixed_coordinate_derivative_cap {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : R3 → V)
    (x : R3) (i : Fin 3) (M : ℝ) (hcap : ‖fderiv ℝ f x‖ ≤ M) :
    ‖directionalFDeriv (coordinateDirection i) f x‖ ≤ M := by
  calc
    _ ≤ ‖fderiv ℝ f x‖*‖coordinateDirection i‖ := (fderiv ℝ f x).le_opNorm _
    _ = ‖fderiv ℝ f x‖ := by rw [norm_coordinateDirection,mul_one]
    _ ≤ M := hcap

/-- The actual mixed angular signed second row, with one constant selected before all profiles and supports. -/
theorem exists_mixedAngularSecond_row_form_bound (hL : 0 < L)
    (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ CLead : ℝ, 0 ≤ CLead ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ data.eta0 →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ u : R3 → Half, ContDiff ℝ ∞ u → (∀ x ∉ K, u x = 0) →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      ∀ l k : Fin 3,
      Integrable (fun x => referenceDensityFamily g L (q,x)*PP (u x)
        (mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q l k x
          (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) u) x))) ∧
      |∫ x, referenceDensityFamily g L (q,x)*PP (u x)
        (mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q l k x
          (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) u) x))| ≤
        CLead*eta*coordinateEnergy coordinateDirection (fun x => referenceDensityFamily g L (q,x))
          (actualReferenceBeta g L q dr Ar p) u := by
  classical
  let capWitness := exists_mixedAngularSecondCoefficient_uniform_first_caps
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hL hreg δ0 W data g2 hg2
  let Q : ℝ := Classical.choose capWitness
  have capFacts := Classical.choose_spec capWitness
  have hQ := capFacts.1
  have hcaps := capFacts.2
  let densityWitness := ActualHigherSScalarCommutatorNativeForm.exists_density_coordinate_relative_bound
    g hg L (closedBall y0 ρ) (isCompact_closedBall _ _)
  let Md : ℝ := Classical.choose densityWitness
  have densityFacts := Classical.choose_spec densityWitness
  have hMd := densityFacts.1
  have hdmu := densityFacts.2
  refine ⟨‖PL‖*Q*(Md+3),by positivity,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 K hK hKball u hu h0 hb hs l k
  have hclosed (x : R3) (hx : x ∈ K) : x ∈ closedBall y0 ρ := ball_subset_closedBall (hKball hx)
  have hc (x : R3) (hx : x ∈ K) :=
    hcaps q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x (hclosed x hx) (hKball hx) (hb x hx) (hs x hx) l k
  have hm : ContDiff ℝ ∞ (fun x => referenceDensityFamily g L (q,x)) := by
    simpa only [Function.comp_def,id] using
      (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hmu (x : R3) : 0 ≤ referenceDensityFamily g L (q,x) := (referenceDensityFamily_pos g hg L (q,x)).le
  have hderiv : ∀ x ∈ K, ‖directionalFDeriv (coordinateDirection l) (mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q l k) x‖ ≤ Q*eta := by
    intro x hx
    exact mixed_coordinate_derivative_cap (mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q l k) x l (Q*eta) (hc x hx).2.2
  have result := weighted_second_operator_form_bound PL (fun x => referenceDensityFamily g L (q,x))
    (actualReferenceBeta g L q dr Ar p) u
    (mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q l k)
    K hK hm (continuous_actualReferenceBeta g hg L q dr Ar p hL hdr hAr)
    (actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp) hu h0
    (fun x hx => (hc x hx).1) Q Md eta hQ (zero_le_one.trans hMd) heta hmu hb l k
    (fun x hx => (hc x hx).2.1) hderiv (fun x hx => hdmu q hq x (hclosed x hx) l)
  simpa only [ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using result


open ActualHigherSScalarCommutatorNativeForm ActualFiniteHarmonicCore

/-- All nine ordered mixed angular second rows, acting on the full Sobolev half input. -/
def mixedAngularSecondNegativeField (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Neg :=
  ∑ l : Fin 3, ∑ k : Fin 3,
    mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q l k x
      (directionalFDeriv (coordinateDirection l)
        (directionalFDeriv (coordinateDirection k) (halfInput hO hD F)) x)

/-- The explicit nine-row mixed angular weak form is small in the original reference energy. -/
theorem exists_mixedAngularSecond_reference_form (hL : 0 < L)
    (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ CRef : ℝ, 0 < CRef ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ data.eta0 →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*PP (halfInput hO hD F x)
        (mixedAngularSecondNegativeField hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q F x)) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*PP (halfInput hO hD F x)
        (mixedAngularSecondNegativeField hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q F x)| ≤
        CRef*eta*∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  let formWitness := exists_mixedAngularSecond_row_form_bound
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hL hreg δ0 W data g2 hg2
  let CLead : ℝ := Classical.choose formWitness
  have formFacts := Classical.choose_spec formWitness
  have hCL := formFacts.1
  have hform := formFacts.2
  let energyWitness := exists_halfInput_coordinate_reference_integral_bound hO hD g hg L hL
    (closedBall y0 ρ) (isCompact_closedBall _ _)
  let Cr : ℝ := Classical.choose energyWitness
  have energyFacts := Classical.choose_spec energyWitness
  have hCr := energyFacts.1
  have henergy := energyFacts.2
  refine ⟨9*(CLead+1)*Cr, by positivity, ?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 K hK hKball F hsupp hb hs
  let u := halfInput hO hD F
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let beta := actualReferenceBeta g L q dr Ar p
  let row : Fin 3 → Fin 3 → R3 → ℝ := fun l k x => mu x*PP (u x)
    (mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q l k x
      (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) u) x))
  have hu : ContDiff ℝ ∞ u := contDiff_halfInput hO hD F
  have hzero : ∀ x ∉ K, u x = 0 := fun x hx =>
    halfInput_eq_zero_off hO hD F x (fun ht => hx (hsupp ht))
  have hrow (l k : Fin 3) := hform q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 K hK hKball u hu hzero hb hs l k
  have hI := ActualHigherSIntegratedPairing.integrable_sum2 row (fun l k => (hrow l k).1)
  have hIEq := ActualHigherSIntegratedPairing.integral_sum2 row (fun l k => (hrow l k).1)
  have hfun : (fun x => mu x*PP (u x)
      (mixedAngularSecondNegativeField hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q F x)) =
      (fun x => ∑ l : Fin 3, ∑ k : Fin 3, row l k x) := by
    funext x
    simp only [mixedAngularSecondNegativeField, halfPairing_sum_right, Finset.mul_sum, row, u]
  have hbcont := continuous_actualReferenceBeta g hg L q dr Ar p hL hdr hAr
  have hbpos := actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp
  have hsub : tsupport F.val ⊆ closedBall y0 ρ := fun x hx => ball_subset_closedBall (hKball (hsupp hx))
  have hE := henergy q hq dr Ar p hdr hAr hp F hsub (fun x hx => hb x (hsupp hx))
  have hN := integrable_finiteCoreReferenceProfileEnergy hO hD g hg L q beta hbcont hbpos F
  let E := ∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F x
  have hE0 : 0 ≤ E := integral_nonneg (fun x =>
    mul_nonneg (referenceDensityFamily_pos g hg L (q,x)).le
      (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q (beta x) (hbpos x).le F x))
  refine ⟨hfun.symm ▸ hI, hN, ?_⟩
  have hIntegral := congrArg (fun f : R3 → ℝ => ∫ x, f x) hfun
  calc
    _ = |∑ l : Fin 3, ∑ k : Fin 3, ∫ x, row l k x| := congrArg abs (hIntegral.trans hIEq)
    _ = ‖∑ l : Fin 3, ∑ k : Fin 3, ∫ x, row l k x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑ l : Fin 3, ‖∑ k : Fin 3, ∫ x, row l k x‖ := norm_sum_le _ _
    _ ≤ ∑ l : Fin 3, ∑ k : Fin 3, ‖∫ x, row l k x‖ := Finset.sum_le_sum (fun l _ => norm_sum_le _ _)
    _ = ∑ l : Fin 3, ∑ k : Fin 3, |∫ x, row l k x| := by simp only [Real.norm_eq_abs]
    _ ≤ ∑ _l : Fin 3, ∑ _k : Fin 3, CLead*eta*coordinateEnergy coordinateDirection mu beta u :=
      Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun k _ => (hrow l k).2))
    _ = 9*CLead*eta*coordinateEnergy coordinateDirection mu beta u := by simp only [Fin.sum_univ_three]; ring
    _ ≤ 9*CLead*eta*(Cr*E) := mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ (9*(CLead+1)*Cr)*eta*E := by
      have hpos : 0 ≤ 9*Cr*eta*E := by positivity
      nlinarith only [hpos]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualMixedAngularPairedGains
