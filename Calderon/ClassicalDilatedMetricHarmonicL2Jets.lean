import Calderon.UniformBufferedHarmonicJetBounds
import Calderon.MetricSmooth
import Calderon.CollaboratorLocalJetsCalcOct17
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
set_option autoImplicit false
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal BigOperators Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity
open EnergyBridge

noncomputable def classicalDilatedMetricHarmonicL2Submodule
    (a : MatrixField) (ha : IsAdmissibleMetric a) (lambda : ℝ)
    (D : Set R3) (hD : IsOpen D) :
    Submodule ℝ (Lp ℝ 2 ((volume : Measure R3).restrict D)) := by
  classical
  -- H0: use only the original metric's smooth coefficient, sampled at lambda • x.
  let A : MatrixField := principalCoefficient (fun y : R3 => a (lambda • y))
  have hA : ContDiff ℝ ∞ A := by
    change ContDiff ℝ ∞ (fun x : R3 => principalCoefficient a (lambda • x))
    exact (contDiff_principalCoefficient a ha).comp (contDiff_const_smul lambda)
  let carrier : Set (Lp ℝ 2 ((volume : Measure R3).restrict D)) :=
    { u : Lp ℝ 2 ((volume : Measure R3).restrict D) |
      ∃ f : R3 → ℝ, ContDiffOn ℝ ∞ f D ∧
        (∀ x ∈ D,
          divCoeffGrad (principalCoefficient (fun y : R3 => a (lambda • y))) f x = 0) ∧
        ∃ hf : MemLp f 2 ((volume : Measure R3).restrict D), hf.toLp f = u }
  exact
    { carrier := carrier
      -- H1: the zero representative satisfies the actual raw scalar PDE identity.
      zero_mem' := by
        have hZeroMem : MemLp (0 : R3 → ℝ) 2 ((volume : Measure R3).restrict D) :=
          MemLp.zero
        refine ⟨(0 : R3 → ℝ), contDiffOn_const, ?_, hZeroMem,
          MemLp.toLp_zero hZeroMem⟩
        intro x _hx
        have hAx : DifferentiableAt ℝ A x := hA.differentiable (by simp) x
        have hZ : ContDiffAt ℝ 2 (0 : R3 → ℝ) x := contDiffAt_const
        have hZero := Jets.divCoeffGrad_smul (A := A) (u := (0 : R3 → ℝ))
          (x := x) (0 : ℝ) hAx hZ
        simpa only [zero_smul, zero_mul] using hZero
      -- H2: addition uses local C2 regularity on the original open domain.
      add_mem' := by
        intro u v hu hv
        obtain ⟨f, hf, hfPDE, hfMem, hfClass⟩ := hu
        obtain ⟨g, hg, hgPDE, hgMem, hgClass⟩ := hv
        refine ⟨f + g, hf.add hg, ?_, hfMem.add hgMem, ?_⟩
        · intro x hx
          have hAx : DifferentiableAt ℝ A x := hA.differentiable (by simp) x
          have hfx : ContDiffAt ℝ 2 f x :=
            (hf.contDiffAt (hD.mem_nhds hx)).of_le (by simp)
          have hgx : ContDiffAt ℝ 2 g x :=
            (hg.contDiffAt (hD.mem_nhds hx)).of_le (by simp)
          change divCoeffGrad A (f + g) x = 0
          rw [Jets.divCoeffGrad_add hAx hfx hgx, hfPDE x hx, hgPDE x hx, add_zero]
        · calc
            (hfMem.add hgMem).toLp (f + g) = hfMem.toLp f + hgMem.toLp g :=
              MemLp.toLp_add hfMem hgMem
            _ = u + v := congrArg₂
              (fun q r : Lp ℝ 2 ((volume : Measure R3).restrict D) => q + r)
              hfClass hgClass
      -- H3: real scalar multiplication preserves the same raw PDE and toLp class.
      smul_mem' := by
        intro r u hu
        obtain ⟨f, hf, hfPDE, hfMem, hfClass⟩ := hu
        refine ⟨r • f, hf.const_smul r, ?_, hfMem.const_smul r, ?_⟩
        · intro x hx
          have hAx : DifferentiableAt ℝ A x := hA.differentiable (by simp) x
          have hfx : ContDiffAt ℝ 2 f x :=
            (hf.contDiffAt (hD.mem_nhds hx)).of_le (by simp)
          change divCoeffGrad A (r • f) x = 0
          rw [Jets.divCoeffGrad_smul r hAx hfx, hfPDE x hx, mul_zero]
        · calc
            (hfMem.const_smul r).toLp (r • f) = r • hfMem.toLp f :=
              MemLp.toLp_const_smul r hfMem
            _ = r • u := congrArg
              (fun q : Lp ℝ 2 ((volume : Measure R3).restrict D) => r • q) hfClass }

theorem exists_uniform_dilated_metric_classical_harmonic_jet_evaluations
    (a : MatrixField) (ha : IsAdmissibleMetric a) (B : ℝ) (hB : 0 < B) :
    ∃ lambda0 : ℝ, 0 < lambda0 ∧ lambda0 ≤ 1 ∧
      ∀ (m : ℕ) (d : ℝ), 0 < d →
      ∃ J : ℝ, 0 < J ∧
      ∀ lambda : ℝ, lambda ∈ Icc (0 : ℝ) lambda0 →
      ∀ (D : Set R3) (hD : IsOpen D), D ⊆ ball (0 : R3) B →
      let H0 := classicalDilatedMetricHarmonicL2Submodule a ha lambda D hD
      ∀ c : R3, closedBall c d ⊆ D →
      ∃ E : H0 →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ,
      ∃ ell : (Fin m → Fin 3) → (H0 →L[ℝ] ℝ),
        ‖E‖ ≤ J ∧
        (∀ alpha : Fin m → Fin 3, ‖ell alpha‖ ≤ J) ∧
        (∀ (alpha : Fin m → Fin 3) (u : H0),
          ell alpha u = E u (fun i : Fin m => EuclideanSpace.single (alpha i) (1 : ℝ))) ∧
        ∀ (u : H0) (f : R3 → ℝ), ContDiffOn ℝ ∞ f D →
          (∀ x ∈ D,
            divCoeffGrad (principalCoefficient (fun y : R3 => a (lambda • y))) f x = 0) →
          ∀ hf : MemLp f 2 ((volume : Measure R3).restrict D),
            hf.toLp f = (u : Lp ℝ 2 ((volume : Measure R3).restrict D)) →
            E u = iteratedFDeriv ℝ m f c := by
  classical
  -- H8: O1 chooses one cutoff before all finite orders and positive buffers.
  obtain ⟨lambda0, hLambda0, hLambda0One, hJet⟩ :=
    exists_uniform_dilated_metric_buffered_harmonic_jet_bound a ha B hB
  refine ⟨lambda0, hLambda0, hLambda0One, ?_⟩
  intro m d hd
  obtain ⟨J, hJ, hBound⟩ := hJet m d hd
  refine ⟨J, hJ, ?_⟩
  intro lambda hLambda D hD hDB
  dsimp only
  intro c hBuffer
  let H0 := classicalDilatedMetricHarmonicL2Submodule a ha lambda D hD
  have hcD : c ∈ D := hBuffer (mem_closedBall_self hd.le)
  -- H4: both directions of the exact toLp-class / AE-representative dictionary.
  have hClassIff (u : Lp ℝ 2 ((volume : Measure R3).restrict D)) (f : R3 → ℝ) :
      (∃ hf : MemLp f 2 ((volume : Measure R3).restrict D), hf.toLp f = u) ↔
        (u : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict D] f := by
    constructor
    · rintro ⟨hf, hfClass⟩
      have he := hf.coeFn_toLp
      rw [hfClass] at he
      exact he
    · intro hu
      have hf : MemLp f 2 ((volume : Measure R3).restrict D) :=
        MemLp.ae_eq hu (Lp.memLp u)
      refine ⟨hf, ?_⟩
      apply Lp.ext
      exact hf.coeFn_toLp.trans hu.symm
  -- H5: ambient open-positive volume and continuity give an ordinary local germ.
  have hJetEq (f g : R3 → ℝ) (hf : ContDiffOn ℝ ∞ f D) (hg : ContDiffOn ℝ ∞ g D)
      (hfg : f =ᵐ[(volume : Measure R3).restrict D] g) :
      iteratedFDeriv ℝ m f c = iteratedFDeriv ℝ m g c := by
    have hEq : EqOn f g D :=
      Measure.eqOn_open_of_ae_eq hfg hD hf.continuousOn hg.continuousOn
    have hGerm : f =ᶠ[nhds c] g :=
      Filter.eventually_of_mem (hD.mem_nhds hcD) (fun _ hx => hEq hx)
    exact (hGerm.iteratedFDeriv ℝ m).eq_of_nhds
  -- H6: choose classical representatives ONLY of the original H0 subtype.
  have hRep (u : H0) : ∃ f : R3 → ℝ, ContDiffOn ℝ ∞ f D ∧
      (∀ x ∈ D,
        divCoeffGrad (principalCoefficient (fun y : R3 => a (lambda • y))) f x = 0) ∧
      (u : Lp ℝ 2 ((volume : Measure R3).restrict D))
        =ᵐ[(volume : Measure R3).restrict D] f := by
    obtain ⟨f, hf, hfPDE, hfMem, hfClass⟩ := u.property
    exact ⟨f, hf, hfPDE, (hClassIff _ f).mp ⟨hfMem, hfClass⟩⟩
  choose rep hSmooth hPDE hAE using hRep
  have hMemClass (u : H0) :
      ∃ hf : MemLp (rep u) 2 ((volume : Measure R3).restrict D),
        hf.toLp (rep u) = (u : Lp ℝ 2 ((volume : Measure R3).restrict D)) :=
    (hClassIff _ (rep u)).mpr (hAE u)
  choose hMem hClass using hMemClass
  -- H7: ordinary order-m jets are real linear on H0, before proving continuity.
  let F : H0 →ₗ[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ :=
    { toFun := fun u => iteratedFDeriv ℝ m (rep u) c
      map_add' := by
        intro u v
        have hSumClass : ((hMem u).add (hMem v)).toLp (rep u + rep v) =
            ((u + v : H0) : Lp ℝ 2 ((volume : Measure R3).restrict D)) := by
          calc
            ((hMem u).add (hMem v)).toLp (rep u + rep v) =
                (hMem u).toLp (rep u) + (hMem v).toLp (rep v) :=
              MemLp.toLp_add (hMem u) (hMem v)
            _ = (u : Lp ℝ 2 ((volume : Measure R3).restrict D)) +
                (v : Lp ℝ 2 ((volume : Measure R3).restrict D)) :=
              congrArg₂
                (fun q r : Lp ℝ 2 ((volume : Measure R3).restrict D) => q + r)
                (hClass u) (hClass v)
            _ = ((u + v : H0) : Lp ℝ 2 ((volume : Measure R3).restrict D)) :=
              (Submodule.coe_add (p := H0) u v).symm
        have hSumAE :
            (((u + v : H0) : Lp ℝ 2 ((volume : Measure R3).restrict D)) : R3 → ℝ)
              =ᵐ[(volume : Measure R3).restrict D] rep u + rep v :=
          (hClassIff _ (rep u + rep v)).mp ⟨(hMem u).add (hMem v), hSumClass⟩
        exact (hJetEq (rep (u + v)) (rep u + rep v) (hSmooth (u + v))
          ((hSmooth u).add (hSmooth v)) ((hAE (u + v)).symm.trans hSumAE)).trans
          (iteratedFDeriv_add_apply
            ((hSmooth u).contDiffAt (hD.mem_nhds hcD) |>.of_le (by simp))
            ((hSmooth v).contDiffAt (hD.mem_nhds hcD) |>.of_le (by simp)))
      map_smul' := by
        intro r u
        have hSmulClass : ((hMem u).const_smul r).toLp (r • rep u) =
            ((r • u : H0) : Lp ℝ 2 ((volume : Measure R3).restrict D)) := by
          calc
            ((hMem u).const_smul r).toLp (r • rep u) =
                r • (hMem u).toLp (rep u) :=
              MemLp.toLp_const_smul r (hMem u)
            _ = r • (u : Lp ℝ 2 ((volume : Measure R3).restrict D)) :=
              congrArg
                (fun q : Lp ℝ 2 ((volume : Measure R3).restrict D) => r • q)
                (hClass u)
            _ = ((r • u : H0) : Lp ℝ 2 ((volume : Measure R3).restrict D)) :=
              (Submodule.coe_smul (p := H0) r u).symm
        have hSmulAE :
            (((r • u : H0) : Lp ℝ 2 ((volume : Measure R3).restrict D)) : R3 → ℝ)
              =ᵐ[(volume : Measure R3).restrict D] r • rep u :=
          (hClassIff _ (r • rep u)).mp ⟨(hMem u).const_smul r, hSmulClass⟩
        exact (hJetEq (rep (r • u)) (r • rep u) (hSmooth (r • u))
          ((hSmooth u).const_smul r) ((hAE (r • u)).symm.trans hSmulAE)).trans
          (iteratedFDeriv_const_smul_apply
            ((hSmooth u).contDiffAt (hD.mem_nhds hcD) |>.of_le (by simp))) }
  -- H8: the bound uses the original volume-restricted Lp norm with factor ONE.
  have hNorm (u : H0) : ‖F u‖ ≤ J * ‖u‖ := by
    have hJetAt := hBound lambda hLambda D hD hDB (rep u)
      (hSmooth u) (hPDE u) (hMem u) c hBuffer
    have hNormClass :
        (eLpNorm (rep u) 2 ((volume : Measure R3).restrict D)).toReal = ‖u‖ := by
      calc
        (eLpNorm (rep u) 2 ((volume : Measure R3).restrict D)).toReal =
            ‖(hMem u).toLp (rep u)‖ := (Lp.norm_toLp (rep u) (hMem u)).symm
        _ = ‖(u : Lp ℝ 2 ((volume : Measure R3).restrict D))‖ :=
          congrArg (fun q : Lp ℝ 2 ((volume : Measure R3).restrict D) => ‖q‖)
            (hClass u)
        _ = ‖u‖ := Submodule.norm_coe (s := H0) u
    rw [hNormClass] at hJetAt
    exact hJetAt
  let E : H0 →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ :=
    F.mkContinuous J hNorm
  have hENorm : ‖E‖ ≤ J := LinearMap.mkContinuous_norm_le F hJ.le hNorm
  have hEValue (u : H0) : E u = F u :=
    LinearMap.mkContinuous_apply F J hNorm u
  have hEJetValue (u : H0) : E u = iteratedFDeriv ℝ m (rep u) c := by
    calc
      E u = F u := hEValue u
      _ = iteratedFDeriv ℝ m (rep u) c := rfl
  have hENormAt (u : H0) : ‖E u‖ ≤ J * ‖u‖ := by
    calc
      ‖E u‖ = ‖F u‖ := congrArg
        (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ => ‖M‖)
        (hEValue u)
      _ ≤ J * ‖u‖ := hNorm u
  -- H9: each canonical ordered-word tuple has product norm ONE, including Fin 0.
  have hTupleNorm (alpha : Fin m → Fin 3) :
      (∏ i : Fin m, ‖EuclideanSpace.single (alpha i) (1 : ℝ)‖) = 1 := by
    simp only [EuclideanSpace.single, PiLp.norm_single, norm_one, Finset.prod_const_one]
  let G (alpha : Fin m → Fin 3) : H0 →ₗ[ℝ] ℝ :=
    { toFun := fun u => E u (fun i : Fin m => EuclideanSpace.single (alpha i) (1 : ℝ))
      map_add' := by
        intro u v
        exact congrArg
          (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ =>
            M (fun i : Fin m => EuclideanSpace.single (alpha i) (1 : ℝ))) (map_add E u v)
      map_smul' := by
        intro r u
        exact congrArg
          (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ =>
            M (fun i : Fin m => EuclideanSpace.single (alpha i) (1 : ℝ))) (map_smul E r u) }
  have hGValue (alpha : Fin m → Fin 3) (u : H0) :
      G alpha u = E u (fun i : Fin m => EuclideanSpace.single (alpha i) (1 : ℝ)) := rfl
  have hScalarBound (alpha : Fin m → Fin 3) (u : H0) : ‖G alpha u‖ ≤ J * ‖u‖ := by
    calc
      ‖G alpha u‖ =
          ‖E u (fun i : Fin m => EuclideanSpace.single (alpha i) (1 : ℝ))‖ :=
        congrArg (fun t : ℝ => ‖t‖) (hGValue alpha u)
      _ ≤ ‖E u‖ * ∏ i : Fin m, ‖EuclideanSpace.single (alpha i) (1 : ℝ)‖ :=
        (E u).le_opNorm (fun i : Fin m => EuclideanSpace.single (alpha i) (1 : ℝ))
      _ = ‖E u‖ * 1 :=
        congrArg (fun t : ℝ => ‖E u‖ * t) (hTupleNorm alpha)
      _ = ‖E u‖ := mul_one ‖E u‖
      _ ≤ J * ‖u‖ := hENormAt u
  let ell (alpha : Fin m → Fin 3) : H0 →L[ℝ] ℝ :=
    (G alpha).mkContinuous J (hScalarBound alpha)
  refine ⟨E, ell, hENorm, ?_, ?_, ?_⟩
  · intro alpha
    exact LinearMap.mkContinuous_norm_le (G alpha) hJ.le (hScalarBound alpha)
  · intro alpha u
    rfl
  -- H5/H6: every classical representative has exactly this full ordinary jet.
  · intro u f hf _hfPDE hfMem hfClass
    exact (hEJetValue u).trans
      (hJetEq (rep u) f (hSmooth u) hf
        ((hAE u).symm.trans ((hClassIff _ f).mp ⟨hfMem, hfClass⟩)))

end OAI.AnisotropicCalderon.Regularity
