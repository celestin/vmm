/*
  Cell Formats
*/
/* UNI Cell Format */
typedef struct packed {
  bit        [3:0]  GFC;
  bit        [7:0]  VPI;
  bit        [15:0] VCI;
  bit               CLP;
  bit        [2:0]  PT;
  bit        [7:0]  HEC;
  bit [0:47] [7:0]  Payload;
} uniType;

/* NNI Cell Format */
typedef struct packed {
  bit        [11:0] VPI;
  bit        [15:0] VCI;
  bit               CLP;
  bit        [2:0]  PT;
  bit        [7:0]  HEC;
  bit [0:47] [7:0]  Payload;
} nniType;

/*
  Union of UNI / NNI / ByteStream
*/
typedef union packed {
  uniType uni;
  nniType nni;
  bit [0:52] [7:0] Mem;
} ATMCellType;

/*
  Cell Rewriting and Forwarding Configuration
*/
typedef struct packed {
  bit [3:0]  FWD;
  bit [11:0] VPI;
} CellCfgType;

typedef union packed {
  CellCfgType Cfg;
  bit [0:1] [7:0] Mem;
} CellCfgMemType;

