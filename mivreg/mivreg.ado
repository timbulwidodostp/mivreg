*! version 1.0.0 2 Oct2018

program define mivreg, byable(onecall)
// Portions of code are from jive.ado
        if _by() {
                local BY `"by `_byvars'`_byrc0':"'
        }
        
        if replay() {
                if `"`e(cmd)'"' != "mivreg" {
                        error 301
                }
                else if _by {
                                error 190
                }
                else {
                        Display `0'
                }
        }
        
        `BY' Estimate `0'

end

program define Estimate, eclass byable(recall)

// Portions of syntax parsing code are from ivreg.ado
        local n 0

        gettoken lhs 0 : 0, parse(" ,[") match(paren)
        IsStop `lhs'
        if `s(stop)' { 
                error 198 
        }  
        while `s(stop)'==0 {
                if "`paren'"=="(" {
                        local n = `n' + 1
                        if `n'>1 {
                                capture noi error 198
di as error `"syntax is "(all instrumented variables = instrument variables)""'
                                exit 198
                        }
                        gettoken p lhs : lhs, parse(" =")
                        while "`p'"!="=" {
                                if "`p'"=="" {
                                        capture noi error 198
di as error `"syntax is "(all instrumented variables = instrument variables)""'
di as error `"the equal sign "=" is required"'
                                        exit 198
                                }
                                local end`n' `end`n'' `p'
                                gettoken p lhs : lhs, parse(" =")
                        }
                        tsunab end`n' : `end`n''
                        tsunab exog`n' : `lhs'
                }
                else {
                        local exog `exog' `lhs'
                }
                gettoken lhs 0 : 0, parse(" ,[") match(paren)
                IsStop `lhs'
        }
        local 0 `"`lhs' `0'"'

        tsunab exog : `exog'
        tokenize `exog'
        local lhs "`1'"
        local 1 " "
        local exog `*'
        
        // Eliminate vars from `exog1' that are in `exog'
        Subtract inst : "`exog1'" "`exog'"
        
        // `lhs' contains depvar, 
        // `exog' contains RHS exogenous variables, 
        // `end1' contains RHS endogenous variables, and
        // `inst' contains the additional instruments

        local lhsname `lhs'
        _find_tsops `lhs'
        if `r(tsops)' {
                qui tsset
                tsrevar `lhs'
                local lhs `r(varlist)'
        }

        local stop 0
		local const_counter 0
        while (`stop' == 0) {
                local oldlist `end1' `inst' `exog' // - problem with a cons term has been solved here somehow
				qui _rmcoll `oldlist'
                local goodlist `r(varlist)' 
                local dropped : list oldlist - goodlist
                if `"`=trim("`dropped'")'"' == "" {
                        local stop 1
                }
				
                foreach x of local dropped {
                        
                        local ininst : list posof "`x'" in inst
                        if `ininst' > 0 {
								di "note: `x' dropped due to collinearity"
                                local inst : subinstr local inst "`x'" ""
                        }
                        local inexog : list posof "`x'" in exog

                        if `inexog' > 0 {
									if `x' != _cons {
										di "note: `x' dropped due to collinearity"
										local exog : subinstr local exog "`x'" ""
									}
									if `x' == _cons {
										local ++const_counter 
									}
									
                        }
                        local inend1 : list posof "`x'" in end1
                        if `inend1' > 0 {
								di "note: `x' dropped due to collinearity"
                                local end1 : subinstr local end1 "`x'" ""
                        }
						
						if `const_counter' > 1 {
							local stop 1		// if only the cons is "problematic" at least 2 times in a row, forget it
						}
                }       
        }

	
		local end1cnt : word count `end1'
        local exogcnt : word count `exog'
        local instcnt : word count `inst'

		tsrevar `end1'
        local end1tsrv `r(varlist)'             
        tsrevar `exog'
        local exogtsrv `r(varlist)'             
        tsrevar `inst'
        local insttsrv `r(varlist)'
		
		if `end1cnt' == 0 {
                di as error "no endogenous regressors"
                exit 198
        }
        CheckOrder `end1cnt' `instcnt'
		
		// Now parse remaining syntax
        syntax [if] [in] , [ Level(cilevel) hom het ROBust FULLer]
        marksample touse
        markout `touse' `lhs' `end1tsrv' `exogtsrv' `insttsrv'
		marksample touse
        markout `touse' `lhs' `end1tsrv' `exogtsrv' `insttsrv'
		
		if `:word count `hom' `het'' > 1 {
                di as error ///
"only one of hom, het may be specified"
                exit 198
        }
		if "`hom'`het'" == "" {
                local hom "hom"           // Default is hom
        }
        
		quietly {
                count if `touse'
                local N = r(N)
				// First stage
                local end1hat ""
				local diagP ""
				tempname fstat1 r21
                foreach z of varlist `end1tsrv' {
                        cap reg `z' `exogtsrv' `insttsrv' if `touse', noconstant
                        if _rc {
                                noi di "A first stage regression failed"
                                exit 498
                        }
                        tempvar `z'pi `z'hat
                        predict double ``z'pi' if `touse'
                        predict double ``z'hat' if `touse', hat    // predicts the diagonal elements 
                
                        local end1hat `end1hat' ``z'pi'
                      	local diagP ``z'hat'

						if `end1cnt' == 1 {
                                cap test `insttsrv'
                                scalar `fstat1' = r(F)
                                local   fstat1n = r(df)
                                local   fstat1d = r(df_r)
                                scalar `r21'   = e(r2)
                        }

                }
		

		// First stage ends here
				
				tempname beta V sigsq
				if "`hom'" != "" {
                        CalcHOM "`lhs'" "`exogtsrv'" "`end1tsrv'"     /*
                               */ "`end1hat'" `touse' `beta'    /*
                               */ `V' `sigsq' "`insttsrv'" "`diagP'" "`robust'" "`fuller'"
                }
				else {
                        CalcHET "`lhs'" "`exogtsrv'" "`end1tsrv'"      /*
                              */ "`end1hat'" `touse' `beta'     /*
                              */ `V' `sigsq' "`insttsrv'" "`diagP'" "`fuller'" 
                }
				matrix colnames `beta' = `end1' `exog' 
                matrix colnames `V' = `end1' `exog' 
                matrix rownames `V' = `end1' `exog' 
                local k `=`end1cnt'+`exogcnt''
				
				eret post `beta' `V', dep(`lhsname') obs(`N')   ///
                        esample(`touse') dof(`=`N'-`k'')
                eret local insts `exog' `inst'
                eret local instd `end1'

		eret scalar jval = J_stat
		eret scalar jpv = Jp_value
		eret local homo = "`hom'"
		eret local jrob = "`robust'"
		eret local fcor = "`fuller'"

                eret local depvar `lhsname'
				eret local title "MIVREG estimation"
				local model `=upper("`hom'`het'")'
				eret local model `model'
                eret scalar rmse = sqrt(`sigsq')
                qui test `end1' `exog'
				eret scalar F = `=r(F)'
                eret scalar df_m = `k'             
                eret scalar df_r = `=`N'-`k''
				tempname rsq adjrsq
                qui sum `lhs'
                sca `rsq' = 1 - (`sigsq'*(`N'-`k') / (r(Var)*(`N'-1)))
                sca `adjrsq' = 1 - (1 - `rsq')*(`N'-1)/(`N'-`k')
                eret scalar r2 = `rsq'
                eret scalar r2_a = `adjrsq'
				if `end1cnt' == 1 {
                        eret scalar F1      = `fstat1'
                        eret scalar df_m_F1 = `fstat1n'
                        eret scalar df_r_F1 = `fstat1d'
                        eret scalar r2_1    = `r21'
                }
				eret local predict "regriv_p"
				eret local cmd `mivreg'

				}

        Display, level(`level')

end

program Display

        syntax , level(cilevel)

        di
        di as text "`e(title)'"  " (`e(model)')"
        di
        
        tempname left right
        .`left' = {}
        .`right' = {}
        
        local C1 "_col(1)"
        local C2 "_col(17)"
        local C3 "_col(54)"
        local C4 "_col(70)"

        if `:word count `e(instd)'' == 1 {
                .`left'.Arrpush `C1' "First-stage summary"
                .`left'.Arrpush `C1' "{hline 25}"
                .`left'.Arrpush `C1' "F("                       ///
                        as res %4.0f e(df_m_F1) as text ","     ///
                        as res %6.0f e(df_r_F1) as text ")"     ///
                        `C2' "= " as res %7.2f e(F1)
                .`left'.Arrpush `C1' "Prob > F" `C2' "= "       ///
                        as res %7.4f Ftail(e(df_m_F1), e(df_r_F1), e(F1))
                .`left'.Arrpush `C1' "R-squared" `C2' "= "      ///
                        as res %7.4f e(r2_1)
				.`left'.Arrpush `C1' "{hline 25}"
        }
        
		
		if "`e(homo)'" == "hom" && "`e(fcor)'" == "fuller" {
				.`left'.Arrpush `C1' "FULL estimation"
		}
		else if "`e(homo)'" == "hom" {
				.`left'.Arrpush `C1' "LIML estimation"
		}
		else if "`e(fcor)'" == "fuller" {
				.`left'.Arrpush `C1' "HFUL estimation"
		}
		else {
				.`left'.Arrpush `C1' "HLIM estimation"
		}
		
		
		if "`e(homo)'" == "hom" && "`e(jrob)'" == "robust" {
				.`left'.Arrpush `C1' "HHN variance estimation"
		}
		else if "`e(homo)'" == "hom" {
				.`left'.Arrpush `C1' "Bekker variance estimation"
		}
		else {
				.`left'.Arrpush `C1' "HNWCS variance estimation"
		}
		
		
		
        .`right'.Arrpush `C3' "Number of obs"           ///
                `C4' "= " as res %7.0f e(N)
        .`right'.Arrpush `C3' "F("                      ///
                as res %4.0f e(df_m) as text ","        ///
                as res %6.0f e(df_r) as text ")"        ///
                `C4' "= " as res %7.2f e(F)
        .`right'.Arrpush `C3' "Prob > F" `C4' "= "      ///
                as res %7.4f Ftail(e(df_m), e(df_r), e(F))
        .`right'.Arrpush `C3' "R-squared"               ///
                `C4' "= " as res %7.4f e(r2)
        .`right'.Arrpush `C3' "Adj R-squared"           ///
                `C4' "= " as res %7.4f e(r2_a)
        .`right'.Arrpush `C3' "Root MSE"                ///
                `C4' "= " as res %7.4f e(rmse)
                
        local nl = `.`left'.arrnels'
        local nr = `.`right'.arrnels'
        local k = max(`nl', `nr')
        forvalues i = 1/`k' {
                di as text `.`left'[`i']' as text `.`right'[`i']'
        }
        
        di
        eret di, level(`level')
        di as text "Instrumented:  " _c
        Disp `e(instd)'
        di as text "Instruments:   " _c
        Disp `e(insts)'
        di as text "{hline 78}"

	if "`e(homo)'" == "hom" && "`e(jrob)'" == "robust" {
		di as text "LO specification test:"
	}
	else if "`e(homo)'" == "hom" {
		di as text "AG specification test:"
	}
	else {
		di as text "CHNSW specification test:"
	}
	di as text "J statistic " _c
	if "`e(jrob)'" == "robust" {
		di as text "(bias-corrected)" _c
	}
	di as text " = " _c
	di as res %7.4f `e(jval)'
	di as text "Prob > J = " _c
	di as res %7.4f `e(jpv)'
	
	di as text "{hline 78}"
        
end

				
program define CalcHOM

		args lhs exog end1 end1hat touse beta V sigsq inst diagP robust fuller J_stat
			

		reg `lhs' `end1hat' `exog' if `touse'
		local N = e(N)
		
		tempvar one
		gen `one' = 1
		//local exog `exog' `one'

		tempname all all2 ZZm ZX ze XctXc ZXc XctpXc  XtPX XtX XtPY XtY Xe_liml Ze_liml XPe_liml XbartPXbar XbartMXbar sigma_bar0 V_N_liml sigma_A1 sigma_A2 sigma_A foreigen alpha_bar Hbar betas_liml  e_liml_e_liml   sig2_liml  liml_exc_kurt   //drop betas, rename it below

		tempname P_sum alpha_r alpha_c

		matrix accum `all' = ///
                		`one' `lhs' `end1' `exog' `inst' `exog' `one' ///
                		if `touse',  nocons

		local end1cnt : word count `end1'
        local exogcnt : word count `exog'
		local k `=`: word count `end1'' + `: word count `exog'' ' 
		local l `=`: word count `inst'' + `: word count `exog'' ' 
                                                      
		matrix `ZZm' = syminv(`all'[`=3+`k''..`=2+`k'+`l'', `=3+`k''..`=2+`k'+`l''])        // (Z'Z)^(-1)
		matrix `ZX' = `all'[`=3+`k''..`=2+`k'+`l'', 3..`=2+`k'']
		matrix `XctXc' = `all'[2..`=2+`k'', 2..`=2+`k'']
		matrix `ZXc' = `all'[`=3+`k''..`=2+`k'+`l'', 2..`=2+`k'']       // 1) transp: from lhs to all x's (both end1 and exog), from inst to exog
		matrix `XctpXc' = `ZXc''*`ZZm'*`ZXc'
		
		matrix `foreigen' = syminv(`XctXc')*`XctpXc'
		matrix eigenvalues `alpha_r' `alpha_c' = `foreigen'
		matrix `alpha_r' = `alpha_r''
		tempvar alpha_r_var
		svmat `alpha_r', name(`alpha_r_var') // make a var
		summ `alpha_r_var' 
		scalar `alpha_bar' = r(min) // take a min value
		
		
		
		if "`fuller'" == "fuller" {
			scalar `alpha_bar' = (`alpha_bar' - (1 - `alpha_bar') * 1 / `N') / (1 - (1 - `alpha_bar') * 1 / `N')

		}

		//matrix `XtPX' = `ZX'' * `ZZm' * `ZX'
		matrix `XtPX' =  `XctpXc'[2..`=1+`k'', 2..`=1+`k'']
		matrix `XtX' = `all'[3..`=2+`k'', 3..`=2+`k'']
		matrix `Hbar' = `XtPX' - `alpha_bar'*`XtX'
		matrix `Hbar' = (`Hbar' + `Hbar'')/2
		
		
		matrix `XtPY' = `ZX''*`ZZm'*`all'[`=3+`k''..`=2+`k'+`l'', 2]
		matrix `XtY' = `all'[3..`=2+`k'', 2]
		matrix `betas_liml' = syminv(`Hbar') * (`XtPY' - `alpha_bar'*`XtY')
		matrix `beta' = `betas_liml''
		matrix `betas_liml' = `betas_liml''
		matrix colnames `betas_liml' = `end1' `exog' 

		tempvar e_liml
		matrix score double `e_liml' = `betas_liml' if `touse'
		replace `e_liml' = `lhs' - `e_liml' if `touse'
		summ `e_liml' if `touse'

		tempvar e_liml_sq
		gen double `e_liml_sq' = `e_liml'^2 if `touse'
		summ `e_liml_sq' if `touse'
		scalar `e_liml_e_liml' = r(sum)
		scalar `sig2_liml' = r(sum)/(r(N) - `k')
		scalar `sigsq' = `sig2_liml'

		tempvar e_liml_sq_diff
		gen double `e_liml_sq_diff' = `e_liml_sq' - `sig2_liml' if `touse'

		tempvar e_liml_qu_diff
		gen double `e_liml_qu_diff' = ((1/`sig2_liml')^2)*(`e_liml'^4) - 3 if `touse'
		summ `e_liml_qu_diff'
		scalar  `liml_exc_kurt' = r(sum)/(r(N))


		// here we start to cook Xbar
		local Xbar ""
		foreach j of varlist `end1' {
                        cap reg `j' `e_liml' if `touse', noconstant
                        if _rc {
                                noi di "A regression of endogenous vars on residuals failed"
                                exit 498
                        }
                        tempvar `j'res
                        predict double ``j'res' if `touse', r
        
                
                        local Xbar `Xbar' ``j'res'
                    
                }


		// here we obtain residuals from regression Xbar on inst
		local MXbar ""
		local MXbarE_liml ""
		foreach p of varlist `Xbar' {		
                        cap reg `p' `inst' `exog' if `touse', noconstant
                        if _rc {
                                noi di "A regression of Xbar  on instruments failed"
                                exit 498
                        }

                        tempvar `p'barres
			//predict double ``p'barres' if `touse'
			predict double ``p'barres' if `touse', r

			tempvar `p'mult
			gen double ``p'mult' = ``p'barres'*`e_liml' if `touse'

                
            local MXbar `MXbar' ``p'barres'        
			local MXbarE_liml `MXbarE_liml' ``p'mult'

                }
			// need to accompany this matrix with columns of zeros for all exog vars
		local zeroCol ""
		tempvar zero
		gen `zero' = 0
		foreach e of varlist `exog' {
			local zeroCol `zeroCol' `zero'
		}


		
		matrix accum `all2' = ///
                		`one' `e_liml' `end1' `exog' `inst' `exog'  `end1hat' `exog' `diagP'  `e_liml_sq' `MXbar' `zeroCol' `Xbar' `zeroCol' `MXbarE_liml' `zeroCol' ///
                		if `touse',  nocons

		matrix `Xe_liml' = `all2'[3..`=2+`k'', 2]
		matrix `Ze_liml' = `all2'[`=3+`k''..`=2+`k' +`l'', 2]
		matrix `XPe_liml' = `ZX''*`ZZm'*`Ze_liml'

		matrix `XbartPXbar' = `XtPX' + (1/`e_liml_e_liml')*(`alpha_bar' * `Xe_liml' * `Xe_liml'' - `Xe_liml'*`XPe_liml'' - `XPe_liml'*`Xe_liml'')
		matrix `XbartMXbar' = `XtX' - (1/`e_liml_e_liml')*(`Xe_liml'*`Xe_liml'') - `XbartPXbar'
		matrix `sigma_bar0' = `sig2_liml' * ( (1-`alpha_bar')^2 * `XbartPXbar' + (`alpha_bar'^2)*`XbartMXbar')

		summ `e_liml_sq' if `touse'		
		matrix `V_N_liml' = r(N)*syminv(`Hbar')*`sigma_bar0'*syminv(`Hbar')

		matrix `sigma_A1' = `all2'[`=3+`k'+`l''..`=2+2*`k'+`l'', `=3+2*`k'+`l'']-(`l'/`N')*`all2'[`=3+`k'+`l''..`=2+2*`k'+`l'', 1]
		matrix `sigma_A2' = `all2'[`=4 +2*`k'+ `l'',`=5 +2*`k'+ `l''..`=4 +3*`k'+ `l'']
		matrix `sigma_A' = `sigma_A1'*(1/`N')*`sigma_A2'

		summ `diagP' if `touse'
		tempvar diagP_sq     // sum of squared diagonal elements
		gen double `diagP_sq' = `diagP'^2 if `touse'
		summ `diagP_sq'
		tempname diagP_sq_ave
		scalar `diagP_sq_ave' = r(sum)/`N'

		tempname sigma_B1 sigma_B2_1 sigma_B2_2 sigma_B
		scalar `sigma_B1' = (`diagP_sq_ave' - (`l'/`N')^2 ) / (1 - 2*`l'/`N' +  `diagP_sq_ave')
		matrix `sigma_B2_1' = `all2'[`=5 +4*`k'+ `l''..`=4 +5*`k'+ `l'',`=5 +4*`k'+ `l''..`=4 +5*`k'+ `l''] 
		matrix `sigma_B2_2' = `sig2_liml'*`all2'[`=5 +2*`k'+ `l''..`=4 +3*`k'+ `l'',`=5 +2*`k'+ `l''..`=4 +3*`k'+ `l'']
		matrix `sigma_B' = `sigma_B1' * (`sigma_B2_1' - `sigma_B2_2')

		tempname Vbar_N Vbar_D
		matrix `Vbar_N' = `N'*syminv(`Hbar')*`sigma_bar0'*syminv(`Hbar')
		matrix `Vbar_D' = `N'*syminv(`Hbar')*(`sigma_bar0' + `sigma_A' + `sigma_A'' + `sigma_B')*syminv(`Hbar')


		// estimation is completed, now specification testing starts
		scalar J_N = (`N' - `k')*`alpha_bar' // the usual J statistic
		scalar J_D = (`N' - `k') * (`alpha_bar' - `l'/`N') // for not necessarily normal distribution
		tempname phi_star_N
		scalar `phi_star_N' = 1 - chi2(`l'-`k', J_N)
		scalar p_val_N = 	1 - normal( invnormal(1-`phi_star_N')/ sqrt(1-`l'/`N'))

 		scalar V_J = 2*`l'/`N' * (1-`l'/`N') + (`diagP_sq_ave' - (`l'/`N')^2) * `liml_exc_kurt'
		scalar p_val_D = 1 - normal(J_D / sqrt(`N' * V_J) )

	if "`robust'" == "robust" {
                matrix `V' = `Vbar_D' * (1/`N')
		scalar J_stat = J_D * (1/`N')
		scalar Jp_value =  p_val_D
        	}
        	else {
                matrix `V' = `Vbar_N' * (1/`N')
		scalar J_stat = J_N * (1/`N')
		scalar Jp_value = p_val_N
        	}


		
end

program define CalcHET

		args lhs exog end1 end1hat touse beta V sigsq inst diagP fuller J_stat
		
		reg `lhs' `end1hat' `exog' if `touse'
		local N = e(N)
		
		tempvar one
		gen `one' = 0
		replace `one' = 1 if `touse'
  
		tempname all all_D ZZm ZX XctXc ZXc XctpXc XctDXc XtPX XtDX XtX Hbar XtPY XtDY XtY betas_hlim e_hlim_e_hlim sig2_hlim
		tempname foreigen alpha_r alpha_c alpha_bar
		tempname all1 PXbar sigma_1 sigma_2 sigma_first sigma_second sigma_final

		matrix accum `all' = ///
                		`one' `lhs' `end1' `exog' `inst' `exog' `one' ///
                		if `touse',  nocons

		local end1cnt : word count `end1'
        local exogcnt : word count `exog'
		local k `=`: word count `end1'' + `: word count `exog'' ' 
		local l `=`: word count `inst'' + `: word count `exog'' ' 
                                                      
		matrix `ZZm' = syminv(`all'[`=3+`k''..`=2+`k'+`l'', `=3+`k''..`=2+`k'+`l''])        // (Z'Z)^(-1)
		matrix `ZX' = `all'[`=3+`k''..`=2+`k'+`l'', 3..`=2+`k'']
		matrix `XctXc' = `all'[2..`=2+`k'', 2..`=2+`k'']
		matrix `ZXc' = `all'[`=3+`k''..`=2+`k'+`l'', 2..`=2+`k'']       // 1) transp: from lhs to all x's (both end1 and exog), from inst to exog
		matrix `XctpXc' = `ZXc''*`ZZm'*`ZXc'
		
		//here we create PXcircle
		local PXc ""
		local Xc `lhs' `end1' `exog'
		foreach j of varlist `Xc' {
						tempvar `j'PX
						gen ``j'PX' = `diagP' * `j' if `touse'
                        local PXc `PXc' ``j'PX'
                    
                }
					
		// then multiply Xcircle by PXcircle			
		matrix accum `all_D' = `Xc' `PXc' if `touse', nocons
		matrix `XctDXc' = `all_D'[1..`=1+`k'',`=2+`k''..`=2+2*`k'']
		
		
		matrix `foreigen' = syminv(`XctXc')*(`XctpXc'-`XctDXc') 
		matrix eigenvalues `alpha_r' `alpha_c' = `foreigen' //find all eigen values
		matrix `alpha_r' = `alpha_r''
		tempvar alpha_r_var
		svmat `alpha_r', name(`alpha_r_var') // make a var
		summ `alpha_r_var' 
		scalar `alpha_bar' = r(min) // take a min value
		
		
		if "`fuller'" == "fuller" {
			scalar `alpha_bar' = (`alpha_bar' - (1 - `alpha_bar') * 1 / `N') / (1 - (1 - `alpha_bar') * 1 / `N')
		}

		matrix `XtPX' =  `XctpXc'[2..`=1+`k'', 2..`=1+`k''] //X'PX
		matrix `XtDX' = `XctDXc'[2..`=1+`k'', 2..`=1+`k''] //X'DX
		matrix `XtX' = `all'[3..`=2+`k'', 3..`=2+`k''] //X'X
		
		matrix `Hbar' = `XtPX' - `XtDX' - `alpha_bar'*`XtX'
		matrix `Hbar' = (`Hbar' + `Hbar'')/2
			
		matrix `XtPY' = `ZX''*`ZZm'*`all'[`=3+`k''..`=2+`k'+`l'', 2]
		matrix `XtDY' = `all_D'[`=3+`k''..`=2+2*`k'',1]
		matrix `XtY' = `all'[3..`=2+`k'', 2]
		
		matrix `betas_hlim' = syminv(`Hbar') * (`XtPY' - `XtDY' - `alpha_bar'*`XtY')
		matrix `beta' = `betas_hlim''
		matrix `betas_hlim' = `betas_hlim''
		matrix colnames `betas_hlim' = `end1' `exog' 	

		tempvar e_hlim
		matrix score double `e_hlim' = `betas_hlim' if `touse'
		replace `e_hlim' = `lhs' - `e_hlim' if `touse'

		tempvar e_hlim_sq 
		gen `e_hlim_sq' = `e_hlim'^2 if `touse'
		summ `e_hlim_sq' if `touse'
		scalar e_hlim_e_hlim = r(sum)
		scalar sig2_hlim = r(sum)/(r(N) - `k')
		scalar `sigsq' = sig2_hlim


		// here we start to cook Xbar
		local Xbar ""
		foreach j of varlist `end1' {
                        cap reg `j' `e_hlim' if `touse', noconstant
                        if _rc {
                                noi di "A regression of an endogenous variable on residuals failed"
                                exit 498
                        }
                        tempvar `j'res
                        predict double ``j'res' if `touse', r
        
                
                        local Xbar `Xbar' ``j'res'
                    
                }
				
		local Xbar `Xbar' `exog'
		
		// here we obtain fitted values from regression Xbar on inst
		local PXbar ""
		local PXbarE_hlim ""
		local PiiXbarE_hlim_sq ""  // P_{ii} * Xbar_{i} * e_{hlim}^{2}
		foreach p of varlist `Xbar' {
				cap reg `p' `inst' `exog' if `touse', noconstant
				if _rc {
                                noi di "A regression of Xbar  on instruments failed"
                                exit 498
                        }
				tempvar `p'barfit
				predict double ``p'barfit' if `touse'
				
				tempvar `p'fitmult
				gen ``p'fitmult' = ``p'barfit'*`e_hlim' if `touse'
				
				tempvar `p'diag_e_hlim_sq
				gen ``p'diag_e_hlim_sq' = `diagP'*`p'*`e_hlim_sq' if `touse'
				
				local PXbar `PXbar' ``p'barfit'        
				local PXbarE_hlim `PXbarE_hlim' ``p'fitmult'
				local PiiXbarE_hlim_sq `PiiXbarE_hlim_sq' ``p'diag_e_hlim_sq'
			}
		
		
		matrix accum `all1' = ///
                		`one' `PXbarE_hlim' `PiiXbarE_hlim_sq' `PXbar' ///
                		if `touse',  nocons
						
		
		
		matrix `sigma_1' = `all1'[2..`=1+`k'',2..`=1+`k'']
		matrix `sigma_2' = `all1'[`=2+2*`k''..`=3*`k'+1',`=2+`k''..`=1+2*`k'']
		matrix `sigma_first' = `sigma_1' - `sigma_2' - `sigma_2''
		
		
		//local Zvars `inst' `exog' // for the second large term
		local Zvars `exog' `inst' 
		
		mata: Z_mat = . // here we start to create the first large term
		//mata: st_view(Z_mat, ., "`inst' `exog'")
		mata: st_view(Z_mat, ., "`exog' `inst'")
		
		putmata insample=`one', replace // create mata vector to use for subsampling
		mata: Z_mat_insample = select(Z_mat, insample) // subsample from Z_mat
		
		//mata: Z_tilda =Z_mat *invsym(cross(Z_mat_insample,Z_mat_insample)) -- slow version of the next line
		mata: Z_tilda = cross(Z_mat_insample', invsym(cross(Z_mat_insample,Z_mat_insample)))
		
		mata: st_matrix("Z_tilda_mat",Z_tilda)
		svmat Z_tilda_mat, name(Z_tilda_var_list)
		
		local Z_tilda_vars "" // create a local with all the variables(columns) from Z_tilda_mat 
		forvalues s = 1/`=colsof(Z_tilda_mat)' {
			local Z_tilda_vars `Z_tilda_vars' Z_tilda_var_list`s'
		}
		
	
		matrix `sigma_second' = J(`k',`k',0)
		scalar V_j_hat = 0
		forvalues p = 1/`l' {
			forvalues r = 1/`l' {
				// create the first term
				local first_var0 `: word `p' of `Z_tilda_vars''
				local second_var0 `: word `r' of `Z_tilda_vars''
				tempvar Z_tilda_vars_e_hlim`p'`r'
				gen `Z_tilda_vars_e_hlim`p'`r'' = `first_var0' * `second_var0' * `e_hlim' if `touse' 
				
				tempname accum_mat0`p'`r'
				matrix accum `accum_mat0`p'`r'' = ///
                		`Z_tilda_vars_e_hlim`p'`r'' `Xbar' ///
                		if `touse',  nocons
				drop `Z_tilda_vars_e_hlim`p'`r'' // not needed anymore
				tempname select_matrix0`p'`r'
				matrix `select_matrix0`p'`r'' = `accum_mat0`p'`r''[2..`=1+`k'',1]
				
				
					// for specification testing
					tempvar Z_tilda_e_hlim_sq`p'`r'
					gen `Z_tilda_e_hlim_sq`p'`r'' = `first_var0' * `second_var0' * `e_hlim_sq' if `touse'	
					summ `Z_tilda_e_hlim_sq`p'`r'' if `touse'	
					tempname sum_Z_tilda_e_hlim_sq`p'`r'
					scalar `sum_Z_tilda_e_hlim_sq`p'`r'' = r(sum)
					drop `Z_tilda_e_hlim_sq`p'`r'' // not needed anymore
			
				// create the second term
				local first_var `: word `p' of `Zvars''
				local second_var `: word `r' of `Zvars''
				tempvar Zvars_e_hlim`p'`r'
				gen `Zvars_e_hlim`p'`r'' = `first_var' * `second_var' * `e_hlim' if `touse' 
			
				tempname accum_mat`p'`r'
				matrix accum `accum_mat`p'`r'' = ///
                		`Zvars_e_hlim`p'`r'' `Xbar' ///
                		if `touse',  nocons
				drop `Zvars_e_hlim`p'`r'' // not needed anymore
				tempname select_matrix`p'`r'
				matrix `select_matrix`p'`r'' = `accum_mat`p'`r''[2..`=1+`k'',1]
				
					// for specification testing
					tempvar Z_e_hlim_sq`p'`r'
					gen `Z_e_hlim_sq`p'`r'' = `first_var' * `second_var' * `e_hlim_sq' if `touse'	
					summ `Z_e_hlim_sq`p'`r'' if `touse'
					tempname sum_Z_e_hlim_sq`p'`r'
					scalar `sum_Z_e_hlim_sq`p'`r'' = r(sum)
					drop `Z_e_hlim_sq`p'`r'' // not needed anymore
				
				//multiply them, and sum up
				matrix `sigma_second' = `sigma_second' + `select_matrix0`p'`r'' * `select_matrix`p'`r'''
				mat drop `select_matrix0`p'`r'' // not needed anymore
				scalar V_j_hat = V_j_hat + `sum_Z_tilda_e_hlim_sq`p'`r'' * `sum_Z_e_hlim_sq`p'`r''
				
			}
		}
		matrix `sigma_final' = `sigma_first' + `sigma_second'
		//HNWCS(2012) variance estimator for the HLIM estimator
		tempname V_bar
		matrix `V_bar' = `N' * syminv(`Hbar') * `sigma_final' * syminv(`Hbar')
		matrix `V' = `V_bar' * (1/`N')
		matrix `V' = (`V' + `V'')/2

		
		tempvar P_ii_sq_e_hlim_qua
		gen `P_ii_sq_e_hlim_qua' = (`diagP'^2) * (`e_hlim'^4) if `touse'
		summ `P_ii_sq_e_hlim_qua' if `touse'
		scalar V_j_hat_2 = r(sum)
		scalar V_j_hat = (V_j_hat - V_j_hat_2)/`l'
		drop `P_ii_sq_e_hlim_qua' // not needed anymore
		
		drop Z_tilda_var_list*
		
		
		// SPECIFICATION testing starts here
		tempname e_z_mat et_Z etPe
		local Zvars `inst' `exog'
		matrix accum `e_z_mat' = ///
                		`e_hlim' `Zvars' ///
                		if `touse',  nocons
		matrix `et_Z' = `e_z_mat'[1, 2..`= 1 + `l'']
		
		tempvar J_stat_diag_term // create e_hlim'*D*e_hlim
		gen `J_stat_diag_term' = `e_hlim'^2 * `diagP' if `touse'
		summ `J_stat_diag_term' if `touse'

		matrix `etPe' = `et_Z' * `ZZm' * `et_Z''
		scalar J_stat = (`etPe'[1,1] - r(sum)) / sqrt(V_j_hat) + `l'
		drop `J_stat_diag_term' // not needed anymore
		
		scalar Jp_value = 1 - chi2(`l'-`k', J_stat)
		
end


// Borrowed from ivreg.ado      
program define IsStop, sclass

        if `"`0'"' == "[" {
                sret local stop 1
                exit
        }
        if `"`0'"' == "," {
                sret local stop 1
                exit
        }
        if `"`0'"' == "if" {
                sret local stop 1
                exit
        }
        if `"`0'"' == "in" {
                sret local stop 1
                exit
        }
        if `"`0'"' == "" {
                sret local stop 1
                exit
        }
        else {
                sret local stop 0
        }

end

// Borrowed from ivreg.ado      
program define Subtract   /* <cleaned> : <full> <dirt> */

        args        cleaned     /*  macro name to hold cleaned list
                */  colon       /*  ":"
                */  full        /*  list to be cleaned
                */  dirt        /*  tokens to be cleaned from full */

        tokenize `dirt'
        local i 1
        while "``i''" != "" {
                local full : subinstr local full "``i''" "", word all
                local i = `i' + 1
        }

        tokenize `full'                 /* cleans up extra spaces */
        c_local `cleaned' `*'

end


// Borrowed from ivreg.ado
program define Disp
        local first ""
        local piece : piece 1 64 of `"`0'"'
        local i 1
        while "`piece'" != "" {
                di as text "`first'`piece'"
                local first "               "
                local i = `i' + 1
                local piece : piece `i' 64 of `"`0'"'
        }
        if `i'==1 { 
                di 
        }

end

// Borrowed from jive.ado
program define CheckOrder 
        
        args end inst

        if `end' > `inst' {
                di as error "equation not identified; must have at " ///
                        "least as many instruments "
                di as error "not in the regression as there are "    ///
                        "instrumented variables"
                exit 481
        }

end

exit
