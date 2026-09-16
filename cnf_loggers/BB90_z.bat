@echo off
if not exist "bv_decide_queries" mkdir "bv_decide_queries"
copy /Y %1 "bv_decide_queries\BB90_z_dist.cnf" >nul
