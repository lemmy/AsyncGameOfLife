//package tlc2.overrides;
//
//import java.io.ByteArrayInputStream;
//import java.io.ByteArrayOutputStream;
//import java.io.IOException;
//import java.util.HashMap;
//import java.util.HashSet;
//import java.util.Map;
//import java.util.Set;
//import java.util.concurrent.ArrayBlockingQueue;
//import java.util.concurrent.CompletableFuture;
//import java.util.concurrent.Executors;
//
//import com.microsoft.azure.servicebus.ExceptionPhase;
//import com.microsoft.azure.servicebus.IMessage;
//import com.microsoft.azure.servicebus.IMessageHandler;
//import com.microsoft.azure.servicebus.ISubscriptionClient;
//import com.microsoft.azure.servicebus.ITopicClient;
//import com.microsoft.azure.servicebus.Message;
//import com.microsoft.azure.servicebus.QueueClient;
//import com.microsoft.azure.servicebus.ReceiveMode;
//import com.microsoft.azure.servicebus.SubscriptionClient;
//import com.microsoft.azure.servicebus.TopicClient;
//import com.microsoft.azure.servicebus.primitives.ConnectionStringBuilder;
//import com.microsoft.azure.servicebus.primitives.ServiceBusException;
//
//import tlc2.value.IValue;
//import tlc2.value.ValueInputStream;
//import tlc2.value.ValueOutputStream;
//import tlc2.value.impl.BoolValue;
//import tlc2.value.impl.RecordValue;
//import tlc2.value.impl.SetEnumValue;
//import tlc2.value.impl.TupleValue;
//import tlc2.value.impl.Value;
//import tlc2.value.impl.ValueVec;
//import util.UniqueString;
//
//// https://docs.microsoft.com/en-us/azure/service-bus-messaging/service-bus-quickstart-portal
//// https://docs.microsoft.com/en-us/azure/service-bus-messaging/service-bus-java-how-to-use-queues
//// https://docs.microsoft.com/en-us/azure/service-bus-messaging/service-bus-queues-topics-subscriptions
//// https://docs.microsoft.com/en-us/azure/service-bus-messaging/service-bus-messages-payloads
//public class Messaging implements IMessageHandler {
//
//	
//	
////	InitialState(procs) == [ p \in procs |-> <<>> ]
//	@TLAPlusOperator(identifier = "InitialState", module = "Messaging", warn = false)
//	public static IValue initialState(final SetEnumValue procs, final SetEnumValue locals) {
//		getInstance().init(procs.elems, locals.elems);
//		return BoolValue.ValTrue;
//	}
//
//	@TLAPlusOperator(identifier = "SendAll", module = "Messaging", warn = false)
//	public static IValue sendAll(final Value mi, final SetEnumValue msgs) {
//		// TODO Move serialization here from out of post. This allows to check if the
//		// elements of msgs are tuples of dst/payload.  Once all are converted into
//		// the format expected by IMessage, they can be send off with
//		// QueueClient#sendBatch. Don't send messages one-by-one to either send all
//		// messages of fail if any one of them cannot be converted.
//		msgs.elements().forEach(msg -> getInstance().post((TupleValue) msg));
//		return mi;
//	}
//	
//	// For technical reasons (OpLambdaValue of the user's Deliver(_,_) lambda does
//	// not correctly eval UNCHANGED), we do not overwrite Messaging!Receive but each
//	// of its conjuncts.  The behavior can be triggered by writing an action with a
//	// TLCExt!TLCNoOp(UNCHANGED <<someVar>>) expression. TLC will throw a
//	// TLCRuntimeException and claim that "In evaluation, the identifier someVar is 
//	// either undefined or not an operator".
//
//	@TLAPlusOperator(identifier = "WaitForMessage", module = "Messaging", warn = false)
//	public static IValue waitForMessage(final Value mi, final Value p) {
//		// This is a no-op, because NextMessage(mi, p) takes care of blocking.
////		return BoolValue.ValTrue;
//		if (getInstance().enabled(p)) {
//			return BoolValue.ValTrue;
//		}
//		return BoolValue.ValFalse;
//	}
//
//	@TLAPlusOperator(identifier = "NextMessage", module = "Messaging", warn = false)
//	public static IValue nextMessage(final Value mi, final Value p) {
//		// receive blocks until an IValue is available.
//		return getInstance().receive(p);
//	}
//	
//	@TLAPlusOperator(identifier = "DeliveredMessage", module = "Messaging", warn = false)
//	public static IValue deliveredMessage(final Value mi, final Value p) {
//		// This translates into mi' = mi, i.e. UNCHANGED mi.
//		return mi;
//	}
//
//	// ***********************************************//
//
//	private static Messaging INSTANCE = null;
//
//	private static synchronized Messaging getInstance() {
//		if (INSTANCE == null) {
//			INSTANCE = new Messaging();
//		}
//		return INSTANCE;
//	}
//
//	// ***********************************************//
//
//	private static final String APPLICATION_TLC = "application/tlc";
//
//	// "Primary Connection String" in Azure portal.
//	private static final String connectionString = System.getProperty("ServiceBusConnectionString", "");
//	private static final String inQueueName = System.getProperty("ServiceBusRecvQueueName", "");
//	private static final String outQueueName = System.getProperty("ServiceBusSendQueueName", "");
//
//	// Produce/Consume one message at a time and block otherwise.
//	private final Map<String, ArrayBlockingQueue<Value>> buffers = new HashMap<>();
//	
//	// Some label to guarantee only messages produced by the currently launched TLC are consumed.
//	private final String label = "AsyncGameOfLife";//String.valueOf(System.currentTimeMillis());
//
//	private ITopicClient sendClient;
//	private ISubscriptionClient receiveClient;
//
//	private final Set<String> locals = new HashSet<>();
//
//	private Messaging() {
//		try {
//			sendClient = new TopicClient(new ConnectionStringBuilder(connectionString, outQueueName), ReceiveMode.PEEKLOCK);
//			
//			receiveClient = new QueueClient(new ConnectionStringBuilder(connectionString, inQueueName), ReceiveMode.PEEKLOCK);
//			
//			ConnectionStringBuilder connectionStringBuilder = new ConnectionStringBuilder(connectionString);
//			SubscriptionClient subscriptionClient = new SubscriptionClient(connectionStringBuilder ,ReceiveMode.PEEKLOCK);
//			subscriptionClient.registerMessageHandler(this, Executors.newSingleThreadExecutor());
//		} catch (InterruptedException | ServiceBusException e) {
//			e.printStackTrace();
//			System.exit(1);
//		}
//	}
//	
//	private void init(ValueVec procs, ValueVec locals) {
//		for (int i = 0; i < procs.size(); i++) {
//			this.buffers.put(procs.elementAt(i).toString(), new ArrayBlockingQueue<>(1));
//		}
//		for (int i = 0; i < locals.size(); i++) {
//			this.locals.add(locals.elementAt(i).toString());
//		}
//    }
//	
//	private boolean enabled(Value p) {
//		return !buffers.get(p.toString()).isEmpty();
//	}
//
//	private Object post(final TupleValue tv) {
//		IValue src = tv.getElem(0);
//		IValue dst = tv.getElem(1);
//		IValue payload = tv.getElem(2);
//		try {
//			final ByteArrayOutputStream bos = new ByteArrayOutputStream();
//			final ValueOutputStream vos = new ValueOutputStream(bos, false);
//			payload.write(vos);
//			vos.close();
//			
//			final Message message = new Message(bos.toByteArray(), APPLICATION_TLC);
//			message.setLabel(label);
//			// Cannot set replyTo here because we have no way of knowing, which node is the
//			// sender. For some specs, the sender might be part of the message, but the
//			// sender is not a parameter of Messaging!Send.
//			message.setReplyTo(src.toString());
//			message.setTo(dst.toString());
//
//			//TODO: Send batch probably performs better.
//			sendClient.send(message);
//		} catch (InterruptedException | ServiceBusException | IOException e) {
//			e.printStackTrace();
//			System.exit(1);
//		}
//		return null;
//	}
//
//	private Value receive(Value p) {
//		try {
//			return buffers.get(p.toString()).take();
//		} catch (InterruptedException e) {
//			e.printStackTrace();
//			System.exit(1);
//		}
//		return null;
//	}
//
//	@Override
//	public void notifyException(Throwable throwable, ExceptionPhase exceptionPhase) {
//		System.err.printf(exceptionPhase + "-" + throwable.getMessage());
//	}
//
//	@Override
//	public CompletableFuture<Void> onMessageAsync(IMessage message) {
//		try {
////			String replyTo = message.getReplyTo();
//			final String to = message.getTo();
//			if (!this.locals.contains(to)) {
//				receiveClient.abandon(message.getLockToken());
//				return CompletableFuture.completedFuture(null);
//			}
//
//			if (message.getContentType() != null && message.getContentType().contentEquals(APPLICATION_TLC)) {
//
//				if (message.getLabel() != null && message.getLabel().contentEquals(label)) {
//					// IMessage#getBody is deprecated:
//					// https://github.com/Azure/azure-service-bus-java/issues/331
//					ValueInputStream vis = new ValueInputStream(
//							new ByteArrayInputStream(message.getMessageBody().getBinaryData().get(0)));
//					try {
//						// See tlc2.overrides.IOUtils.deserialize(StringValue, BoolValue). The internTbl
//						// is needed to map String instances to the "tok" of the UniqueString assigned in
//						// this TLC instance. In other words, two TLC instances might assign different
//						// values for tok to equal Java String instances.
//						Value v = (Value) vis.read(UniqueString.internTbl.toMap());
//						RecordValue rv = (RecordValue) v.toRcd();
//						System.out.printf("\n", rv);
//
//						buffers.get(to).put(v);
//					} finally {
//						vis.close();
//					}
//				} else {
//					System.out.printf("Skipped message with label %s", message.getLabel());
//				}
//			}
//		} catch (InterruptedException | IOException | ServiceBusException e) {
//			e.printStackTrace();
//			System.exit(1);
//		}
//		return CompletableFuture.completedFuture(null);
//	}
//}
