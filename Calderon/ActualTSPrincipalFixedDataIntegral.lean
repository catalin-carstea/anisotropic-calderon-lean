import Calderon.ActualTSPrincipalFirstPhysical
import Calderon.ActualHigherSCommonProfileRoomData
import Calderon.ActualMixedAngularPhysicalBounds

/-! Original fixed-data principal T/S integrability and bound, draft. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalFixedDataIntegral
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  PrincipalCommutator ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
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


open ActualTSPrincipalFirstPhysical ActualTSPrincipalCrossReference
  ActualTSPrincipalPhysicalGreen ActualMixedAngularPairedGains ActualHigherSQuarticFactorization
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "FC" => firstPhysicalCross hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "LC" => literalPrincipalFirstCross hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "Tq" => ActualHigherSFormation.higherSParam L
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)

private lemma factor_four_times_grid (m : ℝ) (f : Fin 3 → Fin 3 → ℝ) :
    m*(4*∑ l : Fin 3, ∑ k : Fin 3, f l k)=4*∑ l : Fin 3, ∑ k : Fin 3, m*f l k := by
  simp only [← Finset.mul_sum]
  ring

attribute [local irreducible] firstPhysicalCross literalPrincipalFirstCross
  finiteCoreReferenceProfileEnergy ActualHigherSFormation.higherSInput

/-- Original factor4 principal T/S row, with genuine integrability and the
unchanged original-energy bound, with all room choices supplied internally. -/
theorem exists_original_principal_TS_integral_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Cprincipal etaPrincipal : ℝ, 0 < Cprincipal ∧ 0 < etaPrincipal ∧ etaPrincipal ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaPrincipal →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*(4*FC g2 dr Ar p q (UF F) x)) ∧
        |∫ x, referenceDensityFamily g L (q,x)*(4*FC g2 dr Ar p q (UF F) x)| ≤
          Cprincipal*eta*∫ x, referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
            hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  let mixed := Classical.choice (exists_actual_mixedAngular_physical_endpoint_room
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
    hL hreg hKernel data.δ0 data.δ0_pos data.germs)
  let ordinary := Classical.choice (exists_principalOrdinaryRoom
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg)
  let G := Classical.choice (exists_common_profile_room_data
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    hL hKernel ordinary.δ ordinary.δ_pos)
  obtain ⟨etaB,heB,_heB0,hBound⟩ := exists_first_physical_cross_reference_bound
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
    hL hreg data.δ0 data.germs mixed
  obtain ⟨Cb,hCb,hB⟩ := hBound g2 hg2
  refine ⟨Cb,min data.eta0 (min G.epsG etaB),hCb,
    lt_min data.eta0_pos (lt_min G.epsG_pos heB),min_le_left _ _,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hsupp hb hs
  have heG : eta ≤ G.epsG := he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heB' : eta ≤ etaB := he.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hT := (G.members q hq dr hdr hdr1 Ar hAr p hp eta heta heG K hK hKball F hsupp hb hs).1
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let f : Fin 3 → Fin 3 → R3 → ℝ := fun l k x => mu x*LC g2 dr Ar p q l k (UF F) x
  have hI (l k : Fin 3) : Integrable (f l k) :=
    integrable_literal_principal_first_cross hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      ordinary g2 hg2 dr Ar p hdr hAr q F hT l k
  have hSum : Integrable (fun x => ∑ l : Fin 3, ∑ k : Fin 3, f l k x) :=
    integrable_finsetSum Finset.univ (fun l _ =>
      integrable_finsetSum Finset.univ (fun k _ => hI l k))
  have hEq : (fun x => mu x*(4*FC g2 dr Ar p q (UF F) x))=
      (fun x => 4*∑ l : Fin 3, ∑ k : Fin 3, f l k x) := by
    funext x
    have hRow := first_physical_cross_eq_literal hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      g2 dr Ar p q (UF F) x
    exact (congrArg (fun t : ℝ => mu x*(4*t)) hRow).trans
      (factor_four_times_grid (mu x) (fun l k => LC g2 dr Ar p q l k (UF F) x))
  exact ⟨hEq.symm ▸ hSum.const_mul 4,
    hB q hq dr hdr hdr1 Ar hAr p hp eta heta heB' F (hsupp.trans hKball)
      (fun x hx => hb x (hsupp hx)) (fun x hx => hs x (hsupp hx))⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalFixedDataIntegral
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalFixedDataIntegral.exists_original_principal_TS_integral_bound
