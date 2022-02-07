include "../../../spec/L1//types.dfy"

module L1_SpecNetwork
{
    import opened L1_SpecTypes

    datatype Network = Network(
        nodes: seq<Address>,
        messagesSentYetToBeReceived: multiset<QbftMessageWithRecipient>,
        time: nat,
        ghost allMessagesSent: multiset<QbftMessageWithRecipient>//,
        // ghost allMessagesSentTo: map<Address, multiset<QbftMessage>>
    )


    predicate NetworkInit(
        e: Network,
        configuration:Configuration
    )
    {
        && e.nodes == configuration.nodes
        && e.messagesSentYetToBeReceived == multiset{}
        && e.time == 0

        && e.allMessagesSent == multiset{}
        // && e.allMessagesSentTo == map n | n in configuration.nodes :: multiset{}
    }

    predicate NetworkDeliverNext(
        e: Network,
        e': Network,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>
    )
    {
        && e'.nodes == e.nodes
        && messagesReceivedByTheNodes <= e.messagesSentYetToBeReceived
        && e'.messagesSentYetToBeReceived == e.messagesSentYetToBeReceived - messagesReceivedByTheNodes + multiset(messagesSentByTheNodes)
        && e'.time == e.time

        && e'.allMessagesSent == e.allMessagesSent + multiset(messagesSentByTheNodes)

    }

    predicate NetworkStutter(
        e: Network,
        e': Network
    )
    {
        e' == e
    }

    predicate NetworkNext(
        e: Network,
        e': Network,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>
    )
    {
        || NetworkDeliverNext(e, e', messagesSentByTheNodes,messagesReceivedByTheNodes)
        || (
            && NetworkStutter(e, e')
            && messagesSentByTheNodes == {}
            && messagesReceivedByTheNodes == multiset{}
        )
    }

    // predicate NetworkUpdateTime(
    //     e: Network,
    //     newTime: nat,
    //     e': Network
    // )
    // {
    //     && newTime > e.time
    //     && e'.nodes == e.nodes
    //     && e'.messagesSentYetToBeReceived == e.messagesSentYetToBeReceived
    //     && e'.time == newTime
    // }
}