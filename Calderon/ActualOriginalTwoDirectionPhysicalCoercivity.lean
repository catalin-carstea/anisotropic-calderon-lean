-- BEFORE-CODE ONLY: Transfer whole consumer successor to Main's scalar-factored v005.
-- Independent native helper checks do not establish the full theorem.
-- Actual reviewed Main forward graph, common replay and before-write approval required.
import Calderon.ActualCommonTraceEndpointRooms
import Calderon.ActualChosenCoverSignedModelCofinalProfile
import Calderon.ActualNativeCoverCommutatorEnergy
import Calderon.ActualPhysicalLowResidualIntegralCap
import Calderon.PhysicalDensityProductsUniformContract
import Calderon.ActualPacketSignedBase
import Calderon.ActualLowerSSelfFormation
import Calderon.ActualPhysicalNormAbsorption
import Calderon.ActualCoercivityPacketNormClosure
import Calderon.ActualFiniteCoreReferenceEnergyLowerBound
import Calderon.ActualFinitePhysicalAdjointOutput
import Calderon.ActualFullForwardPhysicalGraph -- original named pending owned export
import Calderon.ActualChosenCoverFiniteCoercivityGlobalMain

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace BigOperators
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ActualFullEGainedAssembly
  ConformalDepth ReferenceWeightedApproximation ReferenceDensityBounds WeightedBaseSpectral

-- Original public root, unchanged statement. Before-code text only.
theorem exists_two_sided_original_chosen_cover_finite_physical_coercivity
    (original1 original2 : MatrixField) :
    TwoSidedOriginalChosenCoverFinitePhysicalCoercivity original1 original2 := by
  classical
  obtain ⟨tau0,hKernel,hRoomsFor⟩ :=
    MainPhysicalCoercivityAssembly.exists_native_trace_and_cover_endpoint_rooms
  have hOrdered (g1 g2 : MatrixField) :
      OriginalPairChosenCoverFinitePhysicalCoercivity g1 g2 tau0 := by
    intro S hOriginal1 hOriginal2 hXi1 hXi2 hSourceFree hResponse
    obtain ⟨L0,hL0,HCofinalL⟩ := exists_chosen_cover_signed_model_cofinal_profile
      orthogonalSphereHarmonics denseSphereHarmonics sphereFischerInner S
    refine ⟨L0,hL0,?_⟩
    intro L hLge
    have hL : 0 < L := hL0.trans_le hLge
    obtain ⟨cover,hCenter,cRaise,epsMax,hcRaise,hepsMax,hepsMax1,HBetaChoice⟩ :=
      HCofinalL L hLge
    obtain ⟨Rooms,hDataFamily⟩ := hRoomsFor S L hL cover
    let data := Classical.choice hDataFamily
    obtain ⟨theta,hTheta,M,hM,hThetaRange,hThetaSum,hThetaSumGlobal,
        hThetaSupport,hThetaCompact,hKi,HIntegrated⟩ :=
      exists_native_cover_partition_physical_output_referenceProfileEnergy_bounds
        fixedSobolevCalculus fixedDirichletRegularity sphereFischerInner
        orthogonalSphereHarmonics denseSphereHarmonics tau0 hKernel S L hL cover hCenter
    obtain ⟨CL,hCL,HLow⟩ := exists_nativeMixedFirstCorrectionLowOut_uniform_integral_cap
      sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      S.g1 S.g1_admissible S.g2 S.g2_admissible L hL cylinder Geometry.isCompact_cylinder
    have HProducts :=
      CoercivityTransfer.physical_products_uniform_profile_estimate_of_uniform_profile_bound
    have HPacketProducts (i : Fin cover.count) := HProducts
      S.g1 S.g2 S.g1_admissible S.g2_admissible L hL
      (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
      (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
      (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
      fixedSobolevCalculus fixedDirichletRegularity sphereFischerInner
      orthogonalSphereHarmonics denseSphereHarmonics tau0
    choose dP CPi hdP hdPrho hdP1 hCPi HProductsOp HProductsOutput using HPacketProducts
    have HPacketFormation (i : Fin cover.count) :=
      ActualLowerSSelfFormation.exists_uniform_same_packet_higherS_formation
        S.g1 L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
        (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
        (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
        S.g1_admissible fixedSobolevCalculus sphereFischerInner
        orthogonalSphereHarmonics denseSphereHarmonics tau0 (Rooms i)
        fixedDirichletRegularity (data i) hL hKernel S.g2 S.g2_admissible
    choose etaF hEtaF hEtaF0 HFormation using HPacketFormation
    -- Independent same-data signed base combines the checked exact owners.
    have HPacketBase (i : Fin cover.count) :=
      ActualPacketSignedBase.exists_uniform_same_packet_model_higherS_base_norm_lower
        S.g1 L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
        (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
        (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
        S.g1_admissible fixedSobolevCalculus sphereFischerInner
        orthogonalSphereHarmonics denseSphereHarmonics tau0 (Rooms i)
        fixedDirichletRegularity (data i) S.g2 S.g2_admissible hL hKernel cRaise hcRaise
    choose etaBase hEtaBase hEtaBase0 hEtaBase1 HBase using HPacketBase
    -- Original named Main forward export is UNQUALIFIED, not an assumed cap/callback.
    -- Its source/object/receipt must actually qualify before executable materialization.
    have HPacketGraph (i : Fin cover.count) :=
      MainPhysicalGraphBridge.exists_uniform_same_packet_full_physical_graph
        S.g1 L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
        (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
        (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
        S.g1_admissible fixedSobolevCalculus sphereFischerInner
        orthogonalSphereHarmonics denseSphereHarmonics tau0 (Rooms i)
        fixedDirichletRegularity (data i) S.g2 S.g2_admissible hL hKernel
    choose etaGraph hEtaGraph hEtaGraph0 HGraph using HPacketGraph
    -- Pmix/PQ and the literal signed budgets are selected inside HPacketBase.
    let CP : ℝ := 1+∑ i : Fin cover.count,CPi i
    have hCP : 0 < CP := by
      have hs : 0 ≤ ∑ i : Fin cover.count,CPi i := Finset.sum_nonneg (fun i _ => (hCPi i).le)
      dsimp only [CP]
      linarith
    have hCPle (i : Fin cover.count) : CPi i ≤ CP := by
      have hs : CPi i ≤ ∑ j : Fin cover.count,CPi j :=
        Finset.single_le_sum (fun j _ => (hCPi j).le) (Finset.mem_univ i)
      dsimp only [CP]
      linarith
    have hCPsq (i : Fin cover.count) : (CPi i)^2 ≤ CP^2 :=
      pow_le_pow_left₀ (hCPi i).le (hCPle i) 2
    let N : ℝ := (cover.count : ℝ)
    let n : ℝ := max 1 N
    let Q : ℝ := 10000*M^8
    have hN : 0 ≤ N := Nat.cast_nonneg _
    have hn : 1 ≤ n := le_max_left _ _
    have hNn : N ≤ n := le_max_right _ _
    have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
    -- All actual positive thresholds precede BF, degree, profiles and inputs.
    -- etaBase is already the min of the four literal signed-error thresholds.
    let etaPacket : Fin cover.count→ℝ :=
      fun i => min (dP i/2) (min (etaF i) (min (etaBase i) (etaGraph i)))
    have hEtaPacket (i : Fin cover.count) : 0<etaPacket i :=
      lt_min (div_pos (hdP i) (by norm_num))
        (lt_min (hEtaF i) (lt_min (hEtaBase i) (hEtaGraph i)))
    obtain ⟨etaAll,hEtaAll,hEtaAll1,hEtaAllPacket⟩ :=
      MainPhysicalCoercivityAssembly.exists_pos_le_one_and_forall_le etaPacket hEtaPacket
    let etaTarget : ℝ := min epsMax etaAll
    have hEtaTarget : 0<etaTarget := lt_min hepsMax hEtaAll
    have hThresholds (i : Fin cover.count) :
        etaTarget≤dP i/2 ∧ etaTarget≤etaF i ∧
          etaTarget≤etaBase i ∧ etaTarget≤etaGraph i := by
      have h0 : etaTarget≤etaPacket i := (min_le_right _ _).trans (hEtaAllPacket i)
      simpa only [etaPacket,le_min_iff] using h0
    have hEtaKnownP (i : Fin cover.count) : etaTarget≤dP i/2 := (hThresholds i).1
    have hEtaKnownF (i : Fin cover.count) : etaTarget≤etaF i := (hThresholds i).2.1
    -- The genuine physical/Low adjunction theorem is NOT used by this forward norm
    -- argument, is not imported, and contributes NO threshold or extra premise.
    let Blow : ℝ := 1+8*(4*CL+2*CP^2)/cRaise
    let Bcut : ℝ := 1+32*n^2*Q/cRaise
    let BF : ℝ := max Blow Bcut
    obtain ⟨hBlow1,hBlow0,HBudget⟩ :=
      ActualPhysicalNormAbsorption.original_low_products_budget_of_beta_floor CL CP cRaise hCL.le hcRaise
    have hBF1 : 1 ≤ BF := hBlow1.trans (le_max_left _ _)
    have hBudget (eta : ℝ) (heta : 0 ≤ eta) (heta1 : eta ≤ 1) :
        2*CL*((BF^2)⁻¹+eta^2*(BF^4)⁻¹)+2*CP^2*eta^4*(BF^9)⁻¹ ≤ cRaise/8 :=
      HBudget BF (le_max_left _ _) eta heta heta1
    have hBcut : 1+32*n^2*Q/cRaise ≤ BF := le_max_right _ _
    obtain ⟨p0,hp0,HDegree⟩ := HBetaChoice BF
    refine ⟨cover,hCenter,p0,hp0,?_⟩
    intro p hp
    have hpTwo : 2≤p := hp0.trans hp
    have hpOne : 1≤p := le_trans (by decide : 1≤2) hpTwo
    obtain ⟨eps0,heps0,heps0Max,heps0Target,heps01,HRadius⟩ :=
      HDegree p hp etaTarget hEtaTarget
    refine ⟨eps0,heps0,heps01,?_⟩
    intro eps heps hepsle
    have heps1 : eps≤1 := hepsle.trans heps01
    have hepsKnown : eps≤etaTarget := hepsle.trans heps0Target
    obtain ⟨R0,hR0,HSmallRadius⟩ := HRadius eps heps hepsle
    refine ⟨R0,hR0,?_⟩
    intro Rstar hRstar hRstarle
    obtain ⟨HProfile,HModel⟩ := HSmallRadius Rstar hRstar hRstarle
    intro tb htb chi hchi hchiRange hchiSupp hchiDerivative
    let c : ℝ := cRaise/(32*n)
    have hc : 0<c := div_pos hcRaise (mul_pos (by norm_num) (zero_lt_one.trans_le hn))
    refine ⟨c,cover.dilationCeiling,hc,cover.dilation_positive,?_⟩
    intro lambda hlambda hlambdaC delta hdelta hdeltaOne hBootstrap
    have hlambdaOne : lambda≤1 := hlambdaC.trans cover.dilation_le_one
    have hq : lambda∈Icc (0:ℝ) 1 := ⟨hlambda.le,hlambdaOne⟩
    have hqCover : lambda∈Icc (0:ℝ) cover.dilationCeiling := ⟨hlambda.le,hlambdaC⟩
    let R : R3→ℝ := referenceRadius delta Rstar p L
    let beta : R3→ℝ := actualReferenceBeta S.g1 L lambda delta Rstar p
    let mu : R3→ℝ := fun x => referenceDensityFamily S.g1 L (lambda,x)
    let Ki : Fin cover.count→Set R3 := fun i => tsupport (theta i)∩cylinder
    have hProfile (x : R3) (hx : x∈cylinder) :
        BF≤beta x ∧ ‖fderiv ℝ R x‖≤1 ∧ R x*(beta x)^2≤1 ∧ R x<cover.radiusCeiling := by
      have hh := HProfile lambda hq delta hdelta hdeltaOne x hx
      exact ⟨(le_max_right _ _).trans hh.1,hh.2.1.trans heps1,
        hh.2.2.1.trans heps1,hh.2.2.2⟩
    intro A hAS hMean V hVsmooth hVcompact hVS hAllPacketGraph
    have hAInside : tsupport A.val⊆interior cylinder := hAS.trans hchiSupp
    have hVInside : tsupport V⊆interior cylinder := hVS.trans hchiSupp
    let Fi : Fin cover.count→smoothCompactFiniteSphereCore orthogonalSphereHarmonics denseSphereHarmonics :=
      fun i => coreScalar orthogonalSphereHarmonics denseSphereHarmonics (theta i) (hTheta i) A
    let Wi : Fin cover.count→R3→SphereL2 := fun i x => theta i x • V x+
      nativePacketScalarCutoffCommutatorL2 fixedSobolevCalculus sphereFischerInner
        orthogonalSphereHarmonics denseSphereHarmonics tau0 S L cover lambda delta Rstar p
        (theta i) A i x
    let E : smoothCompactFiniteSphereCore orthogonalSphereHarmonics denseSphereHarmonics→R3→ℝ :=
      fun F x => finiteCoreReferenceProfileEnergy orthogonalSphereHarmonics denseSphereHarmonics
        S.g1 S.g1_admissible L lambda (beta x) F x
    have hFiSupport (i : Fin cover.count) : tsupport (Fi i).val⊆tsupport (theta i)∩tsupport A.val := by
      apply closure_minimal ?_ ((isClosed_tsupport (theta i)).inter (isClosed_tsupport A.val))
      intro x hx
      constructor
      · by_contra hn
        have hz : theta i x=0 := image_eq_zero_of_notMem_tsupport hn
        exact (Function.mem_support.1 hx) (by change theta i x • A.val x=0; rw [hz,zero_smul])
      · by_contra hn
        have hz : A.val x=0 := image_eq_zero_of_notMem_tsupport hn
        exact (Function.mem_support.1 hx) (by change theta i x • A.val x=0; rw [hz,smul_zero])
    have hFiKi (i : Fin cover.count) : tsupport (Fi i).val⊆Ki i :=
      fun _ hx => ⟨(hFiSupport i hx).1,interior_subset (hAInside (hFiSupport i hx).2)⟩
    have hFiInside (i : Fin cover.count) : tsupport (Fi i).val⊆interior cylinder :=
      fun _ hx => hAInside (hFiSupport i hx).2
    have hFiMean (i : Fin cover.count) (x : R3) : sphereMean ((Fi i).val x)=0 :=
      mean_zero_coreScalar orthogonalSphereHarmonics denseSphereHarmonics
        (theta i) (hTheta i) A hMean x
    obtain ⟨hWi,hWiInt,hOutput,hPointEnergy,hEnergy⟩ :=
      HIntegrated BF hBF1 p hpOne lambda hqCover delta Rstar hdelta hRstar hProfile
        A hAInside V hVsmooth hVInside hAllPacketGraph
    have hWiInside (i : Fin cover.count) : tsupport (Wi i)⊆interior cylinder :=
      fun _ hx => hAInside ((hWi i).2.2.1 hx).2
    have hWiFi (i : Fin cover.count) : tsupport (Wi i)⊆tsupport (Fi i).val :=
      tsupport_native_cover_physical_output_subset_source fixedSobolevCalculus sphereFischerInner
        orthogonalSphereHarmonics denseSphereHarmonics tau0 S L lambda delta Rstar p cover
        (Fi i) (Wi i) (hWiInside i) (hWi i).2.2.2
    have hFiCylinder (i : Fin cover.count) : tsupport (Fi i).val⊆cylinder :=
      (hFiInside i).trans interior_subset
    have hFiClosedBall (i : Fin cover.count) :
        tsupport (Fi i).val⊆closedBall (cover.packet i).y0 (cover.packet i).rho :=
      fun _ hx => ball_subset_closedBall ((hKi i).2 (hFiKi i hx))
    have hBetaPositive (x : R3) : 0<beta x :=
      actualReferenceBeta_pos S.g1 S.g1_admissible L lambda delta Rstar p hL hdelta hRstar hpOne x
    have hBetaContinuous : Continuous beta :=
      continuous_actualReferenceBeta S.g1 S.g1_admissible L lambda delta Rstar p hL hdelta hRstar
    have hENonneg (F : smoothCompactFiniteSphereCore orthogonalSphereHarmonics denseSphereHarmonics) (x : R3) :
        0≤E F x := finiteCoreReferenceProfileEnergy_nonneg orthogonalSphereHarmonics denseSphereHarmonics
          S.g1 S.g1_admissible L lambda (beta x) (hBetaPositive x).le F x
    have hmu0 (x : R3) : 0 ≤ mu x := (referenceDensityFamily_pos S.g1 S.g1_admissible L (lambda,x)).le
    have hEInt (F : smoothCompactFiniteSphereCore orthogonalSphereHarmonics denseSphereHarmonics) :
        Integrable (fun x => mu x*E F x) :=
      integrable_finiteCoreReferenceProfileEnergy orthogonalSphereHarmonics denseSphereHarmonics
        S.g1 S.g1_admissible L lambda beta hBetaContinuous hBetaPositive F
    have hLowCap (i : Fin cover.count) := HLow fixedDirichletRegularity lambda hq delta Rstar
      hdelta hdeltaOne hRstar p hpTwo eps heps heps1 BF hBF1 (Fi i) (hFiCylinder i)
      (fun x hx => (hProfile x hx).1) (fun x hx => (hProfile x hx).2.1)
      (fun x hx => (HProfile lambda hq delta hdelta hdeltaOne x hx).2.2.1)
    have hProductRoom (i : Fin cover.count) (x : R3) (hx : x∈tsupport (Fi i).val) :
        R x≤dP i ∧ ‖fderiv ℝ R x‖≤1 ∧ BF≤beta x ∧ R x*(beta x)^2≤eps := by
      have hxc := hFiCylinder i hx
      have hh := HProfile lambda hq delta hdelta hdeltaOne x hxc
      have hb1 : 1≤beta x := (le_max_left _ _).trans hh.1
      have hb2 : 1≤(beta x)^2 := by
        simpa only [one_pow] using pow_le_pow_left₀ (zero_le_one : (0 : ℝ) ≤ 1) hb1 2
      have hr0 : 0<R x := referenceRadius_pos delta Rstar p L x hdelta hRstar
      have hrBeta : R x≤R x*(beta x)^2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hb2 hr0.le
      have hr : R x≤eps := hrBeta.trans hh.2.2.1
      have hsmall : eps≤dP i/2 := hepsKnown.trans (hEtaKnownP i)
      exact ⟨(hr.trans hsmall).trans (by linarith only [hdP i]),
        hh.2.1.trans heps1,(le_max_right _ _).trans hh.1,hh.2.2.1⟩
    have hProducts (i : Fin cover.count) := HProductsOutput i lambda hq delta Rstar p
      hdelta hdeltaOne hRstar hpOne eps BF heps.le heps1 hBF1 (Fi i) (hFiClosedBall i)
      (hProductRoom i)
    let productsField {Y : R3 → SphereL2} (_ : ContDiff ℝ ∞ Y) : R3 → SphereL2 := Y
    let ProdF : Fin cover.count → R3 → SphereL2 :=
      fun i => productsField (hProducts i).1
    have hProductsExact (i : Fin cover.count) :
        ContDiff ℝ ∞ (ProdF i) ∧ HasCompactSupport (ProdF i) ∧
          BF^9 * (∫ x, mu x * ‖ProdF i x‖^2) ≤
            (CPi i)^2 * eps^4 * (∫ x, mu x * E (Fi i) x) := by
      have hProdRaw := hProducts i
      dsimp only [ProdF, productsField]
      refine ⟨hProdRaw.1, hProdRaw.2.1, ?_⟩
      simpa only [mu, E, beta] using hProdRaw.2.2.2.2.2.2
    have hProductsCap (i : Fin cover.count) : BF^9*(∫ x,mu x*‖ProdF i x‖^2)≤
        CP^2*eps^4*(∫ x,mu x*E (Fi i) x) := by
      have hi := (hProductsExact i).2.2
      have hIEi : 0≤∫ x,mu x*E (Fi i) x := integral_nonneg (fun x => mul_nonneg (hmu0 x) (hENonneg _ x))
      exact hi.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hCPsq i) (pow_nonneg heps.le 4)) hIEi)
    have hFormation (i : Fin cover.count) := HFormation i lambda hq delta hdelta hdeltaOne
      Rstar hRstar p hpOne eps heps.le (hepsKnown.trans (hEtaKnownF i)) (Ki i) (hKi i).1 (hKi i).2
      (Fi i) (hFiKi i)
      (fun x hx => (le_max_left _ _).trans (HProfile lambda hq delta hdelta hdeltaOne x hx.2).1)
      (fun x hx => (HProfile lambda hq delta hdelta hdeltaOne x hx.2).2.2.1)
    have hModel (i : Fin cover.count) := HModel lambda hq delta hdelta hdeltaOne hBootstrap.1
      (Fi i) (hFiCylinder i) (hFiMean i)
    have hSignedBase (i : Fin cover.count) := HBase i lambda hq delta hdelta hdeltaOne
      Rstar hRstar p hpOne eps heps.le (hepsKnown.trans (hThresholds i).2.2.1)
      (Ki i) (hKi i).1 (hKi i).2 (Fi i) (hFiKi i)
      (fun x hx => (le_max_left _ _).trans (HProfile lambda hq delta hdelta hdeltaOne x hx.2).1)
      (fun x hx => (HProfile lambda hq delta hdelta hdeltaOne x hx.2).2.2.1)
      (fun x hx => hBootstrap.1 x hx.2) (hModel i)
    -- Its first projection is the literal MR+SO bound; exact L1 results remain.
    -- Concrete original fields for the still-open local physical estimate.
    let MRi := fun i : Fin cover.count => nativeModelRaising orthogonalSphereHarmonics
      denseSphereHarmonics sphereFischerInner S.g1 S.g2 S.g1_admissible L lambda delta Rstar p
      S.g2_admissible hdelta hRstar (Fi i)
    let SOi : Fin cover.count→R3→SphereL2 := fun i =>
      ActualHigherSFormation.nativeHigherSOut sphereFischerInner orthogonalSphereHarmonics
        denseSphereHarmonics S.g1 L (cover.packet i).y0 (cover.packet i).Phi
        (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
        (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
        S.g1_admissible fixedSobolevCalculus tau0 delta Rstar p hdelta hRstar lambda
        fixedDirichletRegularity (data i).δ0 (data i).germs S.g2 (Fi i)
    let basei : Fin cover.count→R3→SphereL2 := fun i x => (MRi i).val x+SOi i x
    let Lowi : Fin cover.count→R3→SphereL2 := fun i => nativeMixedFirstCorrectionLowOut
      sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics S.g1 S.g1_admissible
      S.g2 L lambda delta Rstar p hdelta hRstar (Fi i)
    have hmu : Continuous mu :=
      ((contDiff_referenceDensityFamily S.g1 S.g1_admissible L).comp
        (contDiff_const.prodMk contDiff_id)).continuous
    have hPacketPhysical (i : Fin cover.count) :
        (cRaise/8)*(∫ x,mu x*E (Fi i) x)≤∫ x,mu x*‖Wi i x‖^2 := by
      have hCanonical := HGraph i lambda hq delta hdelta hdeltaOne Rstar hRstar p hpTwo eps
        heps.le (hepsKnown.trans (hThresholds i).2.2.2)
        (Ki i) (hKi i).1 (hKi i).2 (Fi i) (hFiKi i)
        (fun x hx => (le_max_left _ _).trans (HProfile lambda hq delta hdelta hdeltaOne x hx.2).1)
        (fun x hx => (HProfile lambda hq delta hdelta hdeltaOne x hx.2).2.2.1)
      let Can : R3 → SphereL2 := productsField hCanonical.1
      have hCanSmooth : ContDiff ℝ ∞ Can := hCanonical.1
      have hCanCompact : HasCompactSupport Can := hCanonical.2.1
      have hCanSupport : tsupport Can ⊆ tsupport (Fi i).val := hCanonical.2.2.2.1
      have hGraphEq : ∀ x ∈ tsupport (Fi i).val,
          MainPhysicalGraphBridge.physicalL2Inclusion orthogonalSphereHarmonics
            denseSphereHarmonics (Wi i x) =
          MainPhysicalGraphBridge.physicalL2Inclusion orthogonalSphereHarmonics
            denseSphereHarmonics (Can x) := by
        intro x hx
        have hNative := (hWi i).2.2.2 i x
          ⟨hFiInside i hx,hThetaSupport i (hFiSupport i hx).1⟩
        have hNativeTyped : sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
            (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (Wi i x))=
            referencePhysicalDensityOperator S.g1 L (cover.packet i).y0
              (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo
              (cover.packet i).Cgeo (cover.packet i).rho (cover.packet i).H
              (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
              S.g1_admissible fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
              denseSphereHarmonics tau0 S.g2 lambda R
              (finiteCoreSobolevLift orthogonalSphereHarmonics denseSphereHarmonics (3/2:ℝ) (Fi i)) x := by
          simpa only [nativePacketPhysicalDensityOperator] using hNative
        have hCanGraph := hCanonical.2.2.2.2 x
        have hWiIncl : MainPhysicalGraphBridge.physicalL2Inclusion orthogonalSphereHarmonics
            denseSphereHarmonics (Wi i x) =
          sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
            (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (Wi i x)) := by
          rfl
        exact hWiIncl.trans (hNativeTyped.trans hCanGraph.symm)
      have hCanSum (x : R3) : Can x = basei i x + Lowi i x + ProdF i x := by
        dsimp only [Can, productsField, basei, MRi, SOi, Lowi, ProdF, R] <;> rfl
      obtain ⟨_hLiftGraph,_hLiftRegular,_hHalfSmooth,_hHalfGraph,_hSGraph,
          hSRegular,_hAllSInt,_hSInt⟩ := (hFormation i).1
      have hBaseContinuous : Continuous (basei i) :=
        (MRi i).property.1.continuous.add hSRegular.1.continuous
      have hBaseCompact : HasCompactSupport (basei i) :=
        (MRi i).property.2.1.add hSRegular.2.2
      have hProdContinuous : Continuous (ProdF i) := (hProductsExact i).1.continuous
      have hProdCompact : HasCompactSupport (ProdF i) := (hProductsExact i).2.1
      have hIEi : 0≤∫ x,mu x*E (Fi i) x :=
        integral_nonneg (fun x => mul_nonneg (hmu0 x) (hENonneg _ x))
      exact TransferPhysicalCoercivity.weighted_packet_norm_lower_of_same_negative_graph
        orthogonalSphereHarmonics denseSphereHarmonics mu hmu hmu0
        (basei i) (Lowi i) (ProdF i) Can (Wi i) (tsupport (Fi i).val)
        (hWiFi i) hCanSupport hGraphEq hBaseContinuous hBaseCompact
        hProdContinuous hProdCompact hCanSmooth.continuous hCanCompact
        hCanSum (∫ x,mu x*E (Fi i) x) cRaise CL CP BF eps
        hIEi hcRaise hBF1 (hSignedBase i).1 (hLowCap i) (hProductsCap i)
        (hBudget eps heps.le heps1)
    have hAInt : Integrable (fun x => mu x*‖A.val x‖^2) :=
      integrable_referenceBase_norm_sq S.g1 S.g1_admissible L lambda A.val
        A.property.1.continuous A.property.2.1
    have hInput (x : R3) (hx : x∈tsupport A.val) : ‖A.val x‖^2≤E A x :=
      norm_finiteCore_eval_sq_le_referenceProfileEnergy
        orthogonalSphereHarmonics denseSphereHarmonics S.g1 S.g1_admissible L lambda
        (beta x) ((le_max_left _ _).trans
          (HProfile lambda hq delta hdelta hdeltaOne x (interior_subset (hAInside hx))).1) A x
    have hOutExact :
        (∑ i : Fin cover.count,∫ x,mu x*‖Wi i x‖^2)≤
        2*(∫ x,mu x*‖V x‖^2)+(2*(cover.count:ℝ)*Q/BF)*(∫ x,mu x*E A x) := by
      simpa only [Q,mul_assoc] using hOutput
    have hFinish := TransferPhysicalCoercivity.weighted_finite_cover_norm_le_of_local_energy
      cover.count mu (E A) A.val V (fun i => E (Fi i)) Wi Q cRaise BF
      hmu0 (hENonneg A) hQ hcRaise hAInt (hEInt A) hInput hBcut hEnergy hPacketPhysical hOutExact
    exact hFinish.2
  exact ⟨tau0,hOrdered original1 original2,hOrdered original2 original1⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
