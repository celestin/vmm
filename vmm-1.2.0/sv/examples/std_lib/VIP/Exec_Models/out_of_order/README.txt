
This example illustrates how to create an in-order atomic
transactor execution model, as described in section titled

      "Out-of-Order Atomic Execution Model"

in Chapter 4, on p175 of the 1st edition of the VMM book.

It uses a simply producer/consumer transactor pair. In a stimulus
stack, the flow of execution would go down toward the DUT. In a
monitoring or response stack, the flow of execution would go away from
the DUT.
