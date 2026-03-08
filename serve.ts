Bun.serve({
  hostname: "0.0.0.0",
  port: 3000,
  async fetch() {
    const html = await Bun.file("dist/index.html").text();
    return new Response(html, {
      headers: { "Content-Type": "text/html" },
    });
  },
});

console.log("Serving on http://0.0.0.0:3000");
