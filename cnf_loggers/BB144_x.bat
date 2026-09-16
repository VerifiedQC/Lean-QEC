@echo off
if not exist "bv_decide_queries" mkdir "bv_decide_queries"
copy /Y %1 "bv_decide_queries\BB144_x_dist.cnf" >nul
