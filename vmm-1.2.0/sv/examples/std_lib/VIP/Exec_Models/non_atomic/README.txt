
This example illustrates how to create a pipelined, concurrent,
split or recurring execution model, as described in section titled

  "Concurrent, Pipelined, Split or Recurring Transaction Execution"

in Chapter 4, on p178 of the 1st edition of the VMM book.

It uses a simply producer/consumer transactor pair. In a stimulus
stack, the flow of execution would go down toward the DUT. In a
monitoring or response stack, the flow of execution would go away from
the DUT.
