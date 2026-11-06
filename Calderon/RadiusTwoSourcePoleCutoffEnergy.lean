import Calderon.RadiusTwoNativeSourceSolution
import Calderon.PrincipalZeroDriftIntegrand
import TauCeti.Analysis.PDE.Caccioppoli.Basic

/-! Full EXPANSION.json precedes this actual zero-source pole-cutoff estimate.
The cutoff may equal one near the outer boundary; actual source truezero is used. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ContDiff Gradient ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))

theorem exists_radiusTwoSource_poleCutoff_energy_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ lam Lam : ℝ, 0 < lam ∧ 0 ≤ Lam ∧ ∀ (f : RadiusTwoL2) (χ : R3 → ℝ),
      ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens, χ x * f x = 0) →
      (∫ x in radiusTwoOpens, χ x ^ 2 *
        ‖TauCeti.W1p.gradient (radiusTwoSourceSolution g hg f : RadiusTwoH1) x‖ ^ 2
          ∂(volume : Measure R3)) ≤
        (2 * Lam / lam) ^ 2 *
          ∫ x in radiusTwoOpens, ‖gradient χ x‖ ^ 2 *
            TauCeti.W1p.value (radiusTwoSourceSolution g hg f : RadiusTwoH1) x ^ 2
              ∂(volume : Measure R3) := by
  obtain ⟨lam,Lam,hEll⟩ := exists_uniformlyEllipticOn_principalCoefficient_radiusTwo g hg
  refine ⟨lam,Lam,hEll.pos,hEll.upper_nonneg,?_⟩
  intro f χ hχ hCompact hχf
  obtain ⟨M,hM,hχM,hgradM⟩ := (hχ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hCompact
  have hχM' : ∀ x ∈ radiusTwoOpens, |χ x| ≤ M := fun x _ => hχM x
  have hgradM' : ∀ x ∈ radiusTwoOpens, ‖gradient χ x‖ ≤ M := fun x _ => hgradM x
  let u : RadiusTwoH1 := (radiusTwoSourceSolution g hg f : RadiusTwoH1)
  let w : RadiusTwoH1 := TauCeti.W1p.contDiffSMul χ hχ hM hχM' hgradM' u
  let v : RadiusTwoH1 := TauCeti.W1p.contDiffSMul χ hχ hM hχM' hgradM' w
  have hu0 : u ∈ TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2 :=
    (radiusTwoSourceSolution g hg f).property
  have hw0 : w ∈ TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2 :=
    TauCeti.W1p.contDiffSMul_mem_w1p0Submodule hχ hM hχM' hgradM' hu0
  have hv0 : v ∈ TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2 :=
    TauCeti.W1p.contDiffSMul_mem_w1p0Submodule hχ hM hχM' hgradM' hw0
  have heq := radiusTwoSourceSolution_equation g hg f ⟨v,hv0⟩
  change TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ) u v =
    TauCeti.PDE.dirichletForcing f ⟨v,hv0⟩ at heq
  rw [TauCeti.PDE.dirichletForcing_apply_eq_setIntegral] at heq
  have hE := hEll.integrable_energyIntegrand_jetField
    (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ)) (beta := 0) (gamma := 0)
    (continuous_principalCoefficient g hg).aestronglyMeasurable
    aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
    (fun _ _ => by simp) u v
  have hpt : ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens,
      lam * (χ x ^ 2 * ‖TauCeti.W1p.gradient u x‖ ^ 2) ≤
        TauCeti.PDE.energyIntegrand (principalCoefficient g x)
          ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)
          (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField v x)
        + lam / 2 * (χ x ^ 2 * ‖TauCeti.W1p.gradient u x‖ ^ 2)
        + 2 * Lam ^ 2 / lam * (‖gradient χ x‖ ^ 2 * TauCeti.W1p.value u x ^ 2) := by
    filter_upwards [ae_restrict_mem radiusTwoOpens.isOpen.measurableSet,
      TauCeti.W1p.gradient_contDiffSMul_ae hχ hM hχM' hgradM' w,
      TauCeti.W1p.gradient_contDiffSMul_ae hχ hM hχM' hgradM' u,
      TauCeti.W1p.value_contDiffSMul_ae hχ hM hχM' hgradM' u] with x hx hgv hgw hvw
    have key := TauCeti.PDE.mul_sq_mul_norm_sq_le_matrixBilinearForm_add hEll.pos (χ x)
      (TauCeti.W1p.value u x) (TauCeti.W1p.gradient u x) (gradient χ x)
      (hEll.lower_bound hx (TauCeti.W1p.gradient u x))
      (hEll.upper_bound hx (gradient χ x) (TauCeti.W1p.gradient u x))
    have hPrincipal : TauCeti.PDE.energyIntegrand (principalCoefficient g x)
        ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)
        (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField v x) =
          TauCeti.PDE.matrixBilinearForm (principalCoefficient g x)
            (TauCeti.W1p.gradient v x) (TauCeti.W1p.gradient u x) := by
      simpa only [Pi.zero_apply,TauCeti.PDE.jetField_apply] using
        principalZeroDrift_energyIntegrand (principalCoefficient g x)
          (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField v x)
    have hvw' : TauCeti.W1p.value w x = χ x * TauCeti.W1p.value u x := by
      simpa only [smul_eq_mul] using hvw
    rw [hPrincipal,hgv,hgw,hvw']
    exact key
  have hZero : (∫ x in radiusTwoOpens, χ x ^ 2 * f x * TauCeti.W1p.value u x
      ∂(volume : Measure R3)) = 0 := by
    calc
      _ = ∫ x in radiusTwoOpens, (0 : ℝ) ∂(volume : Measure R3) := by
        apply integral_congr_ae
        filter_upwards [hχf] with x hx
        calc
          χ x ^ 2 * f x * TauCeti.W1p.value u x =
              χ x * (χ x * f x) * TauCeti.W1p.value u x := by ring
          _ = 0 := by rw [hx,mul_zero,zero_mul]
      _ = 0 := by simp only [integral_zero]
  have hF : (∫ x in radiusTwoOpens, TauCeti.PDE.energyIntegrand (principalCoefficient g x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)
      (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField v x) ∂(volume : Measure R3)) = 0 := by
    rw [← TauCeti.PDE.energyFormH1_def,heq]
    calc
      _ = ∫ x in radiusTwoOpens, χ x ^ 2 * f x * TauCeti.W1p.value u x
          ∂(volume : Measure R3) := by
        apply integral_congr_ae
        filter_upwards [TauCeti.W1p.value_contDiffSMul_ae hχ hM hχM' hgradM' w,
          TauCeti.W1p.value_contDiffSMul_ae hχ hM hχM' hgradM' u] with x hvv hvw
        rw [hvv,hvw,smul_eq_mul,smul_eq_mul]
        ring
      _ = 0 := hZero
  have hBound := TauCeti.PDE.W1p.setIntegral_sq_mul_norm_gradient_sq_le_of_pointwise
    hEll.pos u hχ hχM hgradM hE hpt
    (force := fun _ : R3 => (0 : ℝ)) (by simpa only [integral_zero] using hF.le)
  simpa only [integral_zero,mul_zero,add_zero] using hBound

end OAI.AnisotropicCalderon.ExteriorSource
