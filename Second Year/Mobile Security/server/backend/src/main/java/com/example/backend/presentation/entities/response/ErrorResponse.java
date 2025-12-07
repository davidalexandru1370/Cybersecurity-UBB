package com.example.backend.presentation.entities.response;

public class ErrorResponse<T, I> extends BaseResponse<T> {
    private I initialPayload;
    private int statusCode;
    private String errorMessage;

    public ErrorResponse(I initialPayload, String errorMessage, int statusCode) {
        super(null, statusCode);
        this.initialPayload = initialPayload;
        this.errorMessage = errorMessage;
        this.statusCode = statusCode;
    }
}
