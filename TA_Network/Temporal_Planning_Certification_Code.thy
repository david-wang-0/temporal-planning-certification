theory Temporal_Planning_Certification_Code
  imports TP_NTA_Printing "TA_Certificates.Simple_Network_Language_Certificate_Code"
begin

export_code parse_tp_to_JSON_string
in SML module_name TP_TA_Net_Red file "ML/TA_Network_Reduction.sml"

end