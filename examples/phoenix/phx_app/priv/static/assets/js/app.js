// Vendored globals: phoenix.min.js exposes window.Phoenix,
// phoenix_live_view.min.js exposes window.LiveView.
const csrfToken = document
  .querySelector("meta[name='csrf-token']")
  .getAttribute("content");

const liveSocket = new LiveView.LiveSocket("/live", Phoenix.Socket, {
  params: { _csrf_token: csrfToken },
});
liveSocket.connect();
window.liveSocket = liveSocket;

// Handle flash close
// (you can safely remove this if you don't use the default flash component)
document.querySelectorAll("[role=alert][data-flash]").forEach((el) => {
  el.addEventListener("click", () => {
    el.setAttribute("hidden", "");
  });
});
