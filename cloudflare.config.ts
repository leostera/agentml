import { defineConfig } from "cf/config";
import * as entrypoint from "./src/index.ts" with { type: "cf-worker" };

export default defineConfig({
	worker: {
		name: "agentml",
		compatibilityDate: "2026-10-07",
		entrypoint,
		domains: ["agentml.leostera.dev"],
		assets: {
			notFoundHandling: "single-page-application",
			runWorkerFirst: ["/api/*"],
		},
	},
});
