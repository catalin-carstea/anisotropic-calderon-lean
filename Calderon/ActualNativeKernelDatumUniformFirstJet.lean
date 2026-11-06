import Calderon.ActualCompactCutoffCompositionJetNorm
import Calderon.ActualCommonSupportSobolevFirstJetNorm
import Calderon.ActualMixedKernelNativeH3Datum
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError SphereHarmonic
  ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint

/-- Finite original kernel jets on the SAME packet map control the exact native datum. -/
theorem exists_nativeMixedKernelPullbackHkDatum_uniform_firstJet_bound
    (hcalc : FixedSobolevCalculus) (S : KnownSideSourceData) (L : ℝ)
    (P : NativeNormalPacket S L) (k : ℕ)
    (Q : Set (ℝ × (R3 × ℝ))) (hQ : IsCompact Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Gext : R3×R3→ℝ) (hG : ContDiff ℝ ∞ Gext)
      (v : ℝ × (R3 × ℝ)), v ∈ Q → ∀ M : ℝ, 0 ≤ M →
      (∀ j ≤ k+2, ∀ z ∈ closedBall (0:R3) 3,
        ‖iteratedFDeriv ℝ j Gext (packetEndpoint S L P v.1 v.2.1 v.2.2 z,v.2.1)‖ ≤ M) →
      ‖nativeMixedKernelPullbackHkDatum S L P Gext hG k v‖ ≤ C*M ∧
      ‖fderiv ℝ (nativeMixedKernelPullbackHkDatum S L P Gext hG k) v‖ ≤ C*M := by
  let Theta : (ℝ × (R3 × ℝ)) × R3 → R3×R3 :=
    fun w => (packetEndpoint S L P w.1.1 w.1.2.1 w.1.2.2 w.2,w.1.2.1)
  have hTheta0 : ContDiff ℝ ∞ (fun w : ℝ × (R3×R3) => (P.Phi w.1 w.2 1).1) :=
    P.native_data.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ (fun w : (ℝ × (R3×ℝ))×R3 =>
      packetEndpoint S L P w.1.1 w.1.2.1 w.1.2.2 w.2) :=
    (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta0).comp
      (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  have hTheta : ContDiff ℝ ∞ Theta := hX.prodMk contDiff_fst.snd.fst
  obtain ⟨A,hA,HA⟩ := exists_commonSupport_smoothBallSobolev_firstJet_bound
    (H:=ℝ × (R3×ℝ)) hcalc k
  obtain ⟨B,hB,HB⟩ := exists_compact_cutoff_composition_finite_joint_jet_bound Theta hTheta Q hQ (k+2)
  refine ⟨A*B,mul_pos hA hB,?_⟩
  intro Gext hG v hv M hM hJets
  let g : (ℝ × (R3×ℝ))×R3 → ℝ := fun w => unitBallSmoothCutoff w.2*Gext (Theta w)
  have hg : ContDiff ℝ ∞ g := (unitBallSmoothCutoff.contDiff.comp contDiff_snd).mul (hG.comp hTheta)
  have hz : ∀ t x, x ∉ closedBall (0:R3) 3 → g (t,x)=0 := by
    intro t x hx
    have hdist : 3 ≤ dist x (0:R3) := (not_le.mp (show ¬ dist x (0:R3) ≤ 3 by simpa only [mem_closedBall] using hx)).le
    change unitBallSmoothCutoff x*Gext (Theta (t,x))=0
    rw [unitBallSmoothCutoff.zero_of_le_dist hdist,zero_mul]
  have hBound : ∀ j ≤ k+2, ∀ x:R3, ‖iteratedFDeriv ℝ j g (v,x)‖ ≤ B*M :=
    HB Gext hG v hv M hM hJets
  have h := HA g hg (closedBall (0:R3) 3) (isCompact_closedBall _ _) hz v (B*M)
    (mul_nonneg hB.le hM) hBound
  have hEqual : (fun t => smoothBallSobolev k
      ⟨fun x => g (t,x),SpatialJetFields.contDiff_spatial_slice g hg t⟩) =
      nativeMixedKernelPullbackHkDatum S L P Gext hG k := by
    funext t
    change smoothBallSobolev k _ = smoothBallSobolev k (nativeMixedKernelPullbackDatum S L P Gext hG t)
    apply TauCeti.Wkp.ext k
    apply Lp.ext
    filter_upwards [value_smoothBallSobolev_ae k
      ⟨fun x => g (t,x),SpatialJetFields.contDiff_spatial_slice g hg t⟩,
      value_smoothBallSobolev_ae k (nativeMixedKernelPullbackDatum S L P Gext hG t),
      ae_restrict_mem ballOpens.isOpen.measurableSet] with x hl hr hx
    rw [hl,hr]
    change unitBallSmoothCutoff x*Gext (Theta (t,x))=Gext (Theta (t,x))
    rw [unitBallSmoothCutoff_one_of_mem hx,one_mul]
  have hValue := congrFun hEqual v
  rw [hValue] at h
  rw [hEqual] at h
  simpa only [mul_assoc] using h

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
