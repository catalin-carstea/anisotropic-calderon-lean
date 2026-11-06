import Calderon.MixedKernelConstruction.MixedKernelNativeGlobalEnergy
import Calderon.MixedKernelConstruction.MixedKernelNativeEnergyPhaseJets
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology InnerProductSpace

/-- The ONE global energy equals the previously differentiated SAME native energy on a physical neighborhood. -/
theorem nativeGlobalEnergy_eventuallyEq_nativeEnergyPhase
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (delta Rstar : ℝ) (hd : 0<delta) (hRs : 0<Rstar) (p : ℕ)
    (i : Fin C.count) (y : R3) (hy : y∈(C.packet i).centers)
    (hrR : referenceRadius delta Rstar p L y<R) (z : R3) (hz : ‖z‖=1)
    (rho : R3 × R3 → ℝ)
    (hFamily : ∀ᶠ b : R3 × R3 in 𝓝 (y,z),
      rho (packetEndpoint S L (C.packet i) lam b.1 (referenceRadius delta Rstar p L y) b.2,b.1)=
        (⟪b.2,b.2⟫_ℝ-1)/2) :
    nativeGlobalEnergy S L C lam R delta Rstar p =ᶠ[𝓝 (packetEndpoint S L (C.packet i) lam y
      (referenceRadius delta Rstar p L y) z,y)]
        nativeEnergyPhase (referenceRadius delta Rstar p L y) rho (referenceRadius delta Rstar p L) := by
  let r0 := referenceRadius delta Rstar p L y
  let P := C.packet i
  have hr0 : 0<r0 := referenceRadius_pos delta Rstar p L y hd hRs
  have hrP : r0≤4*P.rho := hrR.le.trans (hRoom.le.trans (C.radius_room i).le)
  let N : (R3 × R3) → R3 × R3 := fun a => (packetEndpoint S L P lam a.1 r0 a.2,a.1)
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  have hf : ContDiff ℝ ∞ (fun a : R3 × R3 => packetEndpoint S L P lam a.1 r0 a.2) :=
    (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd))
  have hN : ContDiff ℝ ∞ N := hf.prodMk contDiff_fst
  have hVel : ‖r0 • z‖<R := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hr0,hz,mul_one] using hrR
  have hc : Continuous (fun a : R3 × R3 => ‖r0 • a.2‖) := (continuous_snd.const_smul r0).norm
  have hOpen : IsOpen {a : R3 × R3 | a.1∈P.centers ∧ ‖r0 • a.2‖<R} :=
    (P.centers_open.preimage continuous_fst).inter (isOpen_lt hc continuous_const)
  have hNear : ∀ᶠ a : R3 × R3 in 𝓝 (y,z), a.1∈P.centers ∧ ‖r0 • a.2‖<R :=
    hOpen.mem_nhds ⟨hy,hVel⟩
  apply eventuallyEq_of_comp_of_actual_local_inverse N hN (y,z)
    (packet_normal_pair_derivative_isInvertible S L P lam ⟨hlam.1,hlam.2.trans C.dilation_le_one⟩
      r0 hr0 hrP y hy z (by simp only [mem_closedBall,dist_zero_right,hz];norm_num))
  filter_upwards [hNear,hFamily] with a ha hfa
  change nativeGlobalEnergy S L C lam R delta Rstar p (packetEndpoint S L P lam a.1 r0 a.2,a.1)=_
  rw [nativeGlobalEnergy_at_packetEndpoint S L C lam hlam R hR hRoom delta Rstar p i a.1 ha.1 r0 a.2 ha.2]
  change (r0^2*⟪a.2,a.2⟫_ℝ-(referenceRadius delta Rstar p L a.1)^2)/2=
    r0^2*(rho (packetEndpoint S L P lam a.1 r0 a.2,a.1)+1/2)-(referenceRadius delta Rstar p L a.1)^2/2
  rw [hfa]
  ring

/-- Exact first and second derivative transfer uses actual physical eventual equality. -/
theorem nativeGlobalEnergy_jets_eq_of_eventuallyEq
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam R delta Rstar : ℝ) (p : ℕ) (r0 : ℝ) (rho : R3 × R3 → ℝ) (q : R3 × R3)
    (hEq : nativeGlobalEnergy S L C lam R delta Rstar p =ᶠ[𝓝 q]
      nativeEnergyPhase r0 rho (referenceRadius delta Rstar p L)) :
    fderiv ℝ (nativeGlobalEnergy S L C lam R delta Rstar p) q=
      fderiv ℝ (nativeEnergyPhase r0 rho (referenceRadius delta Rstar p L)) q ∧
    fderiv ℝ (fderiv ℝ (nativeGlobalEnergy S L C lam R delta Rstar p)) q=
      fderiv ℝ (fderiv ℝ (nativeEnergyPhase r0 rho (referenceRadius delta Rstar p L))) q :=
  ⟨hEq.fderiv_eq,hEq.fderiv.fderiv_eq⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
