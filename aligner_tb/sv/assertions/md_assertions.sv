
// md_assertions.sv - Reglas SVA del protocolo MD (señales planas)
module md_assertions #(
  parameter int ALGN_DATA_WIDTH = 32,
  parameter int BUS_BYTES       = (ALGN_DATA_WIDTH/8),
  parameter int OFFSET_W        = (BUS_BYTES>1)?$clog2(BUS_BYTES):1,
  parameter int SIZE_W          = $clog2(BUS_BYTES)+1
)(
  input  logic                         clk,
  input  logic                         reset_n,
  input  logic                         md_rx_valid,
  input  logic [ALGN_DATA_WIDTH-1:0]   md_rx_data,
  input  logic [OFFSET_W-1:0]          md_rx_offset,
  input  logic [SIZE_W-1:0]            md_rx_size,
  input  logic                         md_rx_ready,
  input  logic                         md_rx_err,
  input  logic                         md_tx_valid,
  input  logic [ALGN_DATA_WIDTH-1:0]   md_tx_data,
  input  logic [OFFSET_W-1:0]          md_tx_offset,
  input  logic [SIZE_W-1:0]            md_tx_size,
  input  logic                         md_tx_ready
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n);

  property p_rx_hold_until_ready;
    md_rx_valid |-> md_rx_valid [*0:$] ##1 md_rx_ready;
  endproperty
  a_rx_hold_until_ready: assert property (p_rx_hold_until_ready);

  property p_rx_fields_stable;
    md_rx_valid && !md_rx_ready |=> ##1 (md_rx_data==$past(md_rx_data) &&
                                         md_rx_offset==$past(md_rx_offset) &&
                                         md_rx_size==$past(md_rx_size));
  endproperty
  a_rx_fields_stable: assert property (p_rx_fields_stable);

  property p_rx_err_only_on_xfer;
    md_rx_err |-> (md_rx_valid && md_rx_ready);
  endproperty
  a_rx_err_only_on_xfer: assert property (p_rx_err_only_on_xfer);

  property p_tx_hold_until_ready;
    md_tx_valid |-> md_tx_valid [*0:$] ##1 md_tx_ready;
  endproperty
  a_tx_hold_until_ready: assert property (p_tx_hold_until_ready);

  property p_tx_fields_stable;
    md_tx_valid && !md_tx_ready |=> ##1 (md_tx_data==$past(md_tx_data) &&
                                         md_tx_offset==$past(md_tx_offset) &&
                                         md_tx_size==$past(md_tx_size));
  endproperty
  a_tx_fields_stable: assert property (p_tx_fields_stable);
endmodule
