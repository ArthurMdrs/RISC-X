load -run $::env(COV_MERGED_DIR)

report_metrics -detail -out $::env(COV_REPORT_DIR) -overwrite