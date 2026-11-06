import Calderon.ActualCoercivityConsumerBoundaries
import Calderon.ActualPhysicalNormAbsorption

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask.TransferPhysicalCoercivity
open DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic

/-- Transfer the original Low and Products absorption to a full physical
packet output after its negative graph is identified on the common support. -/
theorem weighted_packet_norm_lower_of_same_negative_graph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (mu : R3 → ℝ) (hmu : Continuous mu) (hmu0 : ∀ x, 0 ≤ mu x)
    (base low prod canonical W : R3 → SphereL2) (K : Set R3)
    (hW : tsupport W ⊆ K) (hCanS : tsupport canonical ⊆ K)
    (hGraph : ∀ x ∈ K, MainPhysicalGraphBridge.physicalL2Inclusion hO hD (W x) =
      MainPhysicalGraphBridge.physicalL2Inclusion hO hD (canonical x))
    (hbase : Continuous base) (hbaseC : HasCompactSupport base)
    (hprod : Continuous prod) (hprodC : HasCompactSupport prod)
    (hcan : Continuous canonical) (hcanC : HasCompactSupport canonical)
    (hfull : ∀ x, canonical x = base x + low x + prod x)
    (IE cRaise CL CP BF eta : ℝ) (hIE : 0 ≤ IE) (hc : 0 < cRaise)
    (hBF : 1 ≤ BF)
    (hBase : (cRaise/2)*IE ≤ ∫ x,mu x*‖base x‖^2)
    (hLow : (∫ x,mu x*‖low x‖^2) ≤ CL*((BF^2)⁻¹+eta^2*(BF^4)⁻¹)*IE)
    (hProd : BF^9*(∫ x,mu x*‖prod x‖^2) ≤ CP^2*eta^4*IE)
    (hBudget : 2*CL*((BF^2)⁻¹+eta^2*(BF^4)⁻¹)+
      2*CP^2*eta^4*(BF^9)⁻¹ ≤ cRaise/8) :
    (cRaise/8)*IE ≤ ∫ x,mu x*‖W x‖^2 := by
  have hIdent : W = canonical :=
    eq_of_physicalL2Inclusion_eq_on_common_tsupport hO hD W canonical K hW hCanS hGraph
  have hLowEq : low = (fun x => canonical x - base x - prod x) := by
    funext x
    rw [hfull x]
    abel
  have hlow : Continuous low := by
    rw [hLowEq]
    exact (hcan.sub hbase).sub hprod
  have hlowC : HasCompactSupport low := by
    rw [hLowEq]
    exact (hcanC.sub hbaseC).sub hprodC
  have hCanNorm := ActualPhysicalNormAbsorption.weighted_full_norm_lower_of_low_products_budgets
    mu hmu hmu0 base low prod canonical hbase hbaseC hlow hlowC hprod hprodC hcan hcanC
    hfull IE cRaise CL CP BF eta hIE hc hBF hBase hLow hProd hBudget
  rw [hIdent]
  exact hCanNorm.2

end OAI.AnisotropicCalderon.MixedKernelConstructionTask.TransferPhysicalCoercivity
