@echo off
if not exist "bv_decide_queries" mkdir "bv_decide_queries"
copy /Y %1 "bv_decide_queries\BB54_z_dist.cnf" >nul
