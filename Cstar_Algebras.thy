(*  Title:      Bounded-Operators/Cstar_Algebras.thy
    Author:     Dominique Unruh, University of Tartu
    Author:     Jose Manuel Rodriguez Caballero, University of Tartu


*)


theory Cstar_Algebras
  imports "HOL-Library.Adhoc_Overloading" Banach_Algebras
begin

                        
class cCstar_algebra = cbanach_algebra +
  fixes star_involution :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>")
  assumes
\<open> (x + y)\<^sup>\<star> = (x\<^sup>\<star>) +  (y\<^sup>\<star>)\<close>
\<open> ( (c *\<^sub>C x)\<^sup>\<star> ) = (c\<^sup>\<bullet>) *\<^sub>C (x\<^sup>\<star>)\<close>
\<open> ( (x\<degree>y)\<^sup>\<star> ) = ( (y\<degree>x)\<^sup>\<star> )\<close>


\<open> (x\<^sup>\<star>)\<^sup>\<star> = x \<close>

\<open> \<parallel> (x\<^sup>\<star>)\<degree>x \<parallel> = \<parallel>x\<parallel>^2 \<close>

begin
   

end


end