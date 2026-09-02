defmodule PhxAppWeb.CounterLive do
  use PhxAppWeb, :live_view

  @topic "counter"

  def mount(_params, _session, socket) do
    if connected?(socket), do: Phoenix.PubSub.subscribe(PhxApp.PubSub, @topic)
    {:ok, assign(socket, count: 0)}
  end

  def handle_event("inc", _params, socket) do
    n = socket.assigns.count + 1
    Phoenix.PubSub.broadcast_from(PhxApp.PubSub, self(), @topic, {:count, n})
    {:noreply, assign(socket, count: n)}
  end

  def handle_info({:count, n}, socket), do: {:noreply, assign(socket, count: n)}

  def render(assigns) do
    ~H"""
    <div>
      <h1>Count: <span id="count">{@count}</span></h1>
      <button id="inc" phx-click="inc">+1</button>
    </div>
    """
  end
end
